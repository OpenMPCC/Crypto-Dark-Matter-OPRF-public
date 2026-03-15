use std::cmp::min;

use super::{
    base_svole::{Receiver as BaseReceiver, Sender as BaseSender},
    spsvole::{SpsReceiver, SpsSender},
    utils::Powers,
};
use crate::{
    errors::Error,
    svole::{SVoleReceiver, SVoleSender},
};
use generic_array::typenum::Unsigned;
use rand::{
    distributions::{Distribution, Uniform}, CryptoRng, Rng, SeedableRng
};
use scuttlebutt::{
    field::{Degree, FiniteField},
    ring::FiniteRing,
    AbstractChannel, AesRng, Block, Malicious, SemiHonest,
};
use vectoreyes::{Aes128EncryptOnly, AesBlockCipher, SimdBase};

// LPN parameters used in the protocol. We use three stages, two sets of LPN
// parameters for setup, and one set of LPN parameters for the extend phase.
// This differs from what is done in the WYKW paper, but based on personal
// communication with one of the authors, is what is used in the implementation.

/// Type for LPN parameters used internally in the setup phase and the extend phase of the
/// protocol. LPN parameters are provided during the initialization of the protocol so that
/// the extension produces small, medium or large number of values.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LpnParams {
    /// Hamming weight `t` of the error vector `e` used in the LPN assumption.
    weight: usize,
    /// Number of columns `n` in the LPN matrix.
    cols: usize,
    /// Number of rows `k` in the LPN matrix.
    rows: usize,
    /// Extension length
    len: usize,
}

// LPN parameters for setup0 phase.
// const LPN_SETUP0_PARAMS: LpnParams = LpnParams {
//     weight: 600,
//     cols: 9_600, // cols / weight = 16
//     rows: 1_220,
// };

/// Extra Small LPN parameters for setup phase.
pub const LPN_SETUP_EXTRASMALL: LpnParams = LpnParams {
    weight: 600,
    cols: 2_400, // cols / weight = 4
    rows: 1_220,
    len: 2_400,
};
/// Extra Small LPN parameters for extend phase.
pub const LPN_EXTEND_EXTRASMALL: LpnParams = LpnParams {
    weight: 600,
    cols: 9_600, // cols / weight = 4
    rows: 1_220,
    len: 9_600,
};

/// Small LPN parameters for setup phase.
pub const LPN_SETUP_SMALL: LpnParams = LpnParams {
    weight: 600,
    cols: 9_600, // cols / weight = 16
    rows: 1_220,
    len: 9_600,
};
/// Small LPN parameters for extend phase.
pub const LPN_EXTEND_SMALL: LpnParams = LpnParams {
    weight: 2_600,
    cols: 166_400, // cols / weight = 64
    rows: 5_060,
    len: 166_400,
};

/// Medium LPN parameters for setup phase.
pub const LPN_SETUP_MEDIUM: LpnParams = LpnParams {
    weight: 2_600,
    cols: 166_400, // cols / weight = 64
    rows: 5_060,
    len: 166_400,
};
/// Medium LPN parameters for extend phase.
pub const LPN_EXTEND_MEDIUM: LpnParams = LpnParams {
    weight: 4_965,
    cols: 10_168_320, // cols / weight = 2_048
    rows: 158_000,
    len: 10_168_320,
};

/// Large LPN parameters for setup phase.
pub const LPN_SETUP_LARGE: LpnParams = LpnParams {
    rows: 19_870,
    cols: 642_048,
    weight: 2_508,
    len: 642_048,
};
/// Large LPN parameters for extend phase.
pub const LPN_EXTEND_LARGE: LpnParams = LpnParams {
    rows: 589_760,
    cols: 10_805_248,
    weight: 1_319,
    len: 10_805_248,
};

/// Select LPN parameters to minimize the number of extend operations
pub fn choose_lpn_parameters<FE: FiniteField>(num_voles: usize) -> (LpnParams, LpnParams) {
    let mut param = if num_voles >= LPN_EXTEND_MEDIUM.cols - compute_num_saved::<FE>(LPN_EXTEND_MEDIUM) {
        (LPN_SETUP_LARGE, LPN_EXTEND_LARGE)
    } else if num_voles >= LPN_EXTEND_SMALL.cols - compute_num_saved::<FE>(LPN_EXTEND_SMALL) {
        (LPN_SETUP_MEDIUM, LPN_EXTEND_MEDIUM)
    } else if num_voles >= LPN_EXTEND_EXTRASMALL.cols - compute_num_saved::<FE>(LPN_EXTEND_EXTRASMALL) {
        (LPN_SETUP_SMALL, LPN_EXTEND_SMALL)
    } else {
        (LPN_SETUP_EXTRASMALL, LPN_EXTEND_EXTRASMALL)
    };

    let num_saved = compute_num_saved::<FE>(param.1);
    let to_extend = num_voles + num_saved;
    // Ensure that the number of columns is a multiple of the weight.
    let mut factor = 2;
    while factor * param.1.weight < to_extend && factor * param.1.weight < param.1.cols {
        factor *= 2;
    };
    param.1.cols = factor * param.1.weight;
    param.1.len = to_extend;
    param
}

// Constant `d` representing a `d`-local linear code, meaning that each column
// of the LPN matrix contains exactly `d` non-zero entries.
const LPN_PARAMS_D: usize = 10;

// Computes the number of saved VOLEs we need for specific LPN parameters.
fn compute_num_saved<FE: FiniteField>(params: LpnParams) -> usize {
    params.rows + params.weight + Degree::<FE>::USIZE
}

fn lpn_mtx_indices<FE: FiniteField>(
    distribution: &Uniform<u32>,
    mut rng: &mut AesRng,
) -> [(usize, FE::PrimeField); LPN_PARAMS_D] {
    let mut indices = [0u32; LPN_PARAMS_D];
    for i in 0..LPN_PARAMS_D {
        let mut rand_idx = distribution.sample(&mut rng);
        while indices[0..i].iter().any(|&x| x == rand_idx) {
            rand_idx = distribution.sample(&mut rng);
        }
        indices[i] = rand_idx;
    }
    let mut out_indices = [(0, FE::PrimeField::ONE); LPN_PARAMS_D];
    for i in 0..LPN_PARAMS_D {
        out_indices[i].0 = indices[i].try_into().unwrap();
        out_indices[i].1 = FE::PrimeField::random_nonzero(&mut rng);
    }
    out_indices
}

fn lpn_mtx_indices_aes<FE: FiniteField>(
    k: usize,
    k_mask: usize,
    mut rng: &mut AesRng,
) -> [(usize, FE::PrimeField); LPN_PARAMS_D] {
    let mut indices = [0u32; LPN_PARAMS_D];
    let blocks: [vectoreyes::U8x16; Aes128EncryptOnly::BLOCK_COUNT_HINT] = rng.random_bits();
    let b1 = [blocks[0].as_array(), blocks[1].as_array(), blocks[2].as_array(), blocks[3].as_array()].concat();
    for i in 0..4 {
        // Combine 4 bytes into a u32
        let candidate = (b1[i*4] as usize) << 24 |
                        (b1[i*4 + 1] as usize) << 16 |
                        (b1[i*4 + 2] as usize) << 8 |
                        (b1[i*4 + 3] as usize);
        let mut rand_idx = candidate & k_mask;
        if rand_idx >= k {
            rand_idx = rand_idx - k;
        }  
        indices[i] = rand_idx as u32;
    }
    let mut out_indices = [(0, FE::PrimeField::ONE); LPN_PARAMS_D];
    for i in 0..LPN_PARAMS_D {
        out_indices[i].0 = indices[i].try_into().unwrap();
        out_indices[i].1 = FE::PrimeField::random_nonzero(&mut rng);
    }
    out_indices
}

/// Subfield VOLE sender.
pub struct Sender<FE: FiniteField> {
    lpn_setup: LpnParams,
    lpn_extend: LpnParams,
    spsvole: SpsSender<FE>,
    base_voles: Vec<(FE::PrimeField, FE)>,
    base_sender: BaseSender<FE>,
    // Shared RNG with the receiver for generating the LPN matrix.
    lpn_rng: AesRng,
}

impl<FE: FiniteField> Sender<FE> {
    fn send_internal<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        params: LpnParams,
        num_saved: usize,
        rng: &mut RNG,
        output: &mut Vec<(FE::PrimeField, FE)>,
    ) -> Result<(), Error> {
        let old_output_len = output.len();
        let rows = params.rows;
        let cols = params.cols;
        let weight = params.weight;
        let r = Degree::<FE>::USIZE;
        let m = cols / weight;
        // The number of base VOLEs we need to use.
        let used = rows + weight + r;

        debug_assert!(
            self.base_voles.len() >= used,
            "Not enough base sVOLEs: {} < {} + {} + {}",
            self.base_voles.len(),
            rows,
            weight,
            r
        );

        let uws = self
            .spsvole
            .send(channel, m, &self.base_voles[rows..rows + weight + r], rng)?;
        debug_assert_eq!(uws.len(), cols);

        let leftover = self.base_voles.len() - used;

        // The VOLEs we'll save for the next iteration.
        let mut base_voles = Vec::with_capacity(num_saved + leftover);
        // The VOLEs we'll return to the caller.
        let out_len = cols - num_saved;
        let out_len = min(out_len, params.len);
        output.reserve_exact(old_output_len + out_len);
        assert!(rows <= 4_294_967_295); // 2^32 -1

        let mut k_mask = 1;
        while k_mask < rows {
            k_mask <<= 1;
            k_mask |= 1;
        }

        for (i, (e, c)) in uws.into_iter().enumerate() {
            let indices = lpn_mtx_indices_aes::<FE>(rows, k_mask, &mut self.lpn_rng);
            // Compute `x := u A + e` and `z := w A + c`, where `A` is the LPN matrix.
            let mut x = e;
            let mut z = c;
            for i in 0..10{
                unsafe{
                    // prefect eleemnt self.base_voles[indicies[1]]
                    core::arch::x86_64::_mm_prefetch(
                        self.base_voles.as_ptr().add(indices[i].0) as *const i8,
                        core::arch::x86_64::_MM_HINT_T0,
                    );
                }
            }

            /*
            for (j, a) in indices.iter() {
                x += self.base_voles[*j].0 * *a;
                z += *a * self.base_voles[*j].1;
            }
            */

            // Prefetch implementation. ~ 10% increase in speed.
            for i in 0..10{
                let (j, a) = indices[i];
                x += self.base_voles[j].0 * a;
                z += a * self.base_voles[j].1;
            }
            
            
            if i < num_saved {
                base_voles.push((x, z));
            } else {
                output.push((x, z));
            }
            if output.len() >= params.len{
                break;
            }
        }
        base_voles.extend(self.base_voles[used..].iter());
        self.base_voles = base_voles;
        debug_assert_eq!(self.base_voles.len(), num_saved + leftover);
        debug_assert_eq!(output.len(), old_output_len + out_len);
        Ok(())
    }

    /// Init given a OT instance for spsvole
    pub fn init_from_ot<C: AbstractChannel, RNG: CryptoRng + Rng, FF: FiniteField>(
        channel: &mut C,
        mut rng: &mut RNG,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
        sender: &Sender<FF>,
    ) -> Result<Self, Error> {
        
        let ot = sender.extract_base_sender().extract_copee().extract_ot();
        let pows: Powers<FE> = Default::default();
        let mut base_sender = BaseSender::<FE>::init_with_ot(channel, pows.clone(), rng, ot)?;
        let base_voles_setup = base_sender.send(
            channel,
            compute_num_saved::<FE>(lpn_setup),
            &mut AesRng::from_rng(&mut rng).expect("random number generation shouldn't fail"),
        )?;
        
        let ot = sender.extract_spsvole().extract_ot();
        let spsvole = SpsSender::<FE>::init_with_ot(channel, pows, rng, ot)?;
        let seed = rng.gen::<Block>();
        let seed = scuttlebutt::cointoss::receive(channel, &[seed])?[0];
        let lpn_rng = AesRng::from_seed(seed);
        let mut sender = Self {
            lpn_setup,
            lpn_extend,
            spsvole,
            base_voles: base_voles_setup,
            base_sender,
            lpn_rng,
        };

        let mut base_voles_setup = Vec::new();
        sender.send_internal(channel, sender.lpn_setup, 0, rng, &mut base_voles_setup)?;
        sender.base_voles = base_voles_setup;
        // let mut base_voles_extend = Vec::new();
        // sender.send_internal(channel, LPN_SETUP_PARAMS, 0, rng, &mut base_voles_extend)?;
        // sender.base_voles = base_voles_extend;
        Ok(sender)
    }

    /// Init given a OT instance for spsvole
    pub fn init_from_ot_receiver<C: AbstractChannel, RNG: CryptoRng + Rng, FF: FiniteField>(
        channel: &mut C,
        mut rng: &mut RNG,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
        sender: &Receiver<FF>,
    ) -> Result<Self, Error> {
        
        let ot = sender.extract_spsvole().extract_ot();
        let pows: Powers<FE> = Default::default();
        let mut base_sender = BaseSender::<FE>::init_with_ot(channel, pows.clone(), rng, ot)?;
        let base_voles_setup = base_sender.send(
            channel,
            compute_num_saved::<FE>(lpn_setup),
            &mut AesRng::from_rng(&mut rng).expect("random number generation shouldn't fail"),
        )?;
        
        let ot = sender.extract_base_receiver().extract_copee().extract_ot();
        let spsvole = SpsSender::<FE>::init_with_ot(channel, pows, rng, ot)?;
        let seed = rng.gen::<Block>();
        let seed = scuttlebutt::cointoss::receive(channel, &[seed])?[0];
        let lpn_rng = AesRng::from_seed(seed);
        let mut sender = Self {
            lpn_setup,
            lpn_extend,
            spsvole,
            base_voles: base_voles_setup,
            base_sender,
            lpn_rng,
        };

        let mut base_voles_setup = Vec::new();
        sender.send_internal(channel, sender.lpn_setup, 0, rng, &mut base_voles_setup)?;
        sender.base_voles = base_voles_setup;
        // let mut base_voles_extend = Vec::new();
        // sender.send_internal(channel, LPN_SETUP_PARAMS, 0, rng, &mut base_voles_extend)?;
        // sender.base_voles = base_voles_extend;
        Ok(sender)
    }
}

impl<FE: FiniteField> SVoleSender for Sender<FE> {
    type Msg = FE;

    fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        mut rng: &mut RNG,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
    ) -> Result<Self, Error> {
        let pows: Powers<FE> = Default::default();
        let mut base_sender = BaseSender::<FE>::init(channel, pows.clone(), rng)?;
        let base_voles_setup = base_sender.send(
            channel,
            compute_num_saved::<FE>(lpn_setup),
            &mut AesRng::from_rng(&mut rng).expect("random number generation shouldn't fail"),
        )?;
        let spsvole = SpsSender::<FE>::init(channel, pows, rng)?;
        let seed = rng.gen::<Block>();
        let seed = scuttlebutt::cointoss::receive(channel, &[seed])?[0];
        let lpn_rng = AesRng::from_seed(seed);
        let mut sender = Self {
            lpn_setup,
            lpn_extend,
            spsvole,
            base_voles: base_voles_setup,
            base_sender,
            lpn_rng,
        };

        let mut base_voles_setup = Vec::new();
        sender.send_internal(channel, sender.lpn_setup, 0, rng, &mut base_voles_setup)?;
        sender.base_voles = base_voles_setup;
        // let mut base_voles_extend = Vec::new();
        // sender.send_internal(channel, LPN_SETUP_PARAMS, 0, rng, &mut base_voles_extend)?;
        // sender.base_voles = base_voles_extend;
        Ok(sender)
    }

    fn send<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        output: &mut Vec<(FE::PrimeField, FE)>,
    ) -> Result<(), Error> {
        self.send_internal(
            channel,
            self.lpn_extend,
            compute_num_saved::<FE>(self.lpn_extend),
            rng,
            output,
        )
    }

    fn duplicate<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<Self, Error> {
        let mut base_voles = Vec::new();
        self.send_internal(
            channel,
            self.lpn_setup,
            compute_num_saved::<FE>(self.lpn_setup),
            rng,
            &mut base_voles,
        )?;
        // let mut extras = Vec::new();
        // self.send_internal(
        //     channel,
        //     LPN_SETUP_PARAMS,
        //     compute_num_saved::<FE>(LPN_SETUP_PARAMS),
        //     rng,
        //     &mut extras,
        // )?;
        // base_voles.extend(extras.into_iter());

        debug_assert!(base_voles.len() >= compute_num_saved::<FE>(self.lpn_extend));
        debug_assert!(self.base_voles.len() >= compute_num_saved::<FE>(self.lpn_extend));

        let spsvole = self.spsvole.duplicate(channel, rng)?;
        let base_sender = self.base_sender.clone();
        let lpn_rng = self.lpn_rng.fork();
        Ok(Self {
            lpn_setup: self.lpn_setup,
            lpn_extend: self.lpn_extend,
            spsvole,
            base_voles,
            base_sender,
            lpn_rng,
        })
    }
}

/// Subfield VOLE receiver.
pub struct Receiver<FE: FiniteField> {
    lpn_setup: LpnParams,
    lpn_extend: LpnParams,
    spsvole: SpsReceiver<FE>,
    delta: FE,
    base_voles: Vec<FE>,
    base_receiver: BaseReceiver<FE>,
    // Shared RNG with the sender for generating the LPN matrix.
    lpn_rng: AesRng,
}

impl<FE: FiniteField> Receiver<FE> {
    fn receive_internal<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        params: LpnParams,
        num_saved: usize,
        rng: &mut RNG,
        output: &mut Vec<FE>,
    ) -> Result<(), Error> {
        let old_output_len = output.len();
        let rows = params.rows;
        let cols = params.cols;
        let weight = params.weight;
        let r = Degree::<FE>::USIZE;
        let m = cols / weight;
        // The number of base VOLEs we need to use.
        let used = rows + weight + r;

        debug_assert!(
            self.base_voles.len() >= used,
            "{} < {} + {} + {}",
            self.base_voles.len(),
            rows,
            weight,
            r
        );

        let leftover = self.base_voles.len() - used;

        let vs =
            self.spsvole
                .receive(channel, m, &self.base_voles[rows..rows + weight + r], rng)?;
        debug_assert!(vs.len() == cols);
        let mut base_voles = Vec::with_capacity(num_saved + leftover);
        let out_len = cols - num_saved;
        let out_len = min(out_len, params.len);
        output.reserve_exact(old_output_len + out_len);
        assert!(rows <= 4_294_967_295); // 2^32 -1

        let mut k_mask = 1;
        while k_mask < rows {
            k_mask <<= 1;
            k_mask |= 1;
        }

        for (i, b) in vs.into_iter().enumerate() {
            let indices = lpn_mtx_indices_aes::<FE>(rows, k_mask, &mut self.lpn_rng);
            let mut y = b;

            for i in 0..10{
                unsafe{
                    // prefect eleemnt self.base_voles[indicies[1]]
                    core::arch::x86_64::_mm_prefetch(
                        self.base_voles.as_ptr().add(indices[i].0) as *const i8,
                        core::arch::x86_64::_MM_HINT_T0,
                    );
                }
            }

            for i in 0..10{
                let (j, a) = indices[i];
                y += a * self.base_voles[j];
            }

            //y += indices.iter().map(|(j, a)| *a * self.base_voles[*j]).sum();

            if i < num_saved {
                base_voles.push(y);
            } else {
                output.push(y);
            }
            if output.len() >= params.len{
                break;
            }
        }
        base_voles.extend(self.base_voles[used..].iter());
        self.base_voles = base_voles;
        debug_assert_eq!(output.len(), old_output_len + out_len);
        Ok(())
    }

    /// Init given a OT instance for spsvole
    pub fn init_from_ot<C: AbstractChannel, RNG: CryptoRng + Rng, FF: FiniteField>(
        channel: &mut C,
        rng: &mut RNG,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
        receiver: &Receiver<FF>,
    ) -> Result<Self, Error>{

        let ot = receiver.extract_base_receiver().extract_copee().extract_ot();
        let pows: Powers<FE> = Default::default();
        let mut base_receiver = BaseReceiver::<FE>::init_with_ot(channel, pows.clone(), rng, ot)?;
        let base_voles_setup =
            base_receiver.receive(channel, compute_num_saved::<FE>(lpn_setup), rng)?;
        let delta = base_receiver.delta();

        let ot = receiver.extract_spsvole().extract_ot();
        let spsvole = SpsReceiver::<FE>::init_with_ot(channel, pows, delta, rng, ot)?; // Dereference reuse_ot
        let seed = rng.gen::<Block>();
        let seed = scuttlebutt::cointoss::send(channel, &[seed])?[0];
        let lpn_rng = AesRng::from_seed(seed);
        let mut receiver = Self {
            lpn_setup,
            lpn_extend,
            spsvole,
            delta,
            base_voles: base_voles_setup,
            base_receiver,
            lpn_rng,
        };
        let mut base_voles_setup = Vec::new();
        receiver.receive_internal(channel, lpn_setup, 0, rng, &mut base_voles_setup)?;
        receiver.base_voles = base_voles_setup;
        // let mut base_voles_extend = Vec::new();
        // receiver.receive_internal(channel, LPN_SETUP_PARAMS, 0, rng, &mut base_voles_extend)?;
        // receiver.base_voles = base_voles_extend;
        Ok(receiver)
    }

    /// Init given a OT instance for spsvole
    pub fn init_from_ot_sender<C: AbstractChannel, RNG: CryptoRng + Rng, FF: FiniteField>(
        channel: &mut C,
        rng: &mut RNG,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
        receiver: &Sender<FF>,
    ) -> Result<Self, Error>{

        let ot = receiver.extract_spsvole().extract_ot();
        let pows: Powers<FE> = Default::default();
        let mut base_receiver = BaseReceiver::<FE>::init_with_ot(channel, pows.clone(), rng, ot)?;
        let base_voles_setup =
        base_receiver.receive(channel, compute_num_saved::<FE>(lpn_setup), rng)?;
        let delta = base_receiver.delta();
        
        let ot = receiver.extract_base_sender().extract_copee().extract_ot();
        let spsvole = SpsReceiver::<FE>::init_with_ot(channel, pows, delta, rng, ot)?; // Dereference reuse_ot
        let seed = rng.gen::<Block>();
        let seed = scuttlebutt::cointoss::send(channel, &[seed])?[0];
        let lpn_rng = AesRng::from_seed(seed);
        let mut receiver = Self {
            lpn_setup,
            lpn_extend,
            spsvole,
            delta,
            base_voles: base_voles_setup,
            base_receiver,
            lpn_rng,
        };
        let mut base_voles_setup = Vec::new();
        receiver.receive_internal(channel, lpn_setup, 0, rng, &mut base_voles_setup)?;
        receiver.base_voles = base_voles_setup;
        // let mut base_voles_extend = Vec::new();
        // receiver.receive_internal(channel, LPN_SETUP_PARAMS, 0, rng, &mut base_voles_extend)?;
        // receiver.base_voles = base_voles_extend;
        Ok(receiver)
    }

    /// Init picked delta
    pub fn init_with_picked_delta<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
        delta: FE,
    ) -> Result<Self, Error> {
        let pows: Powers<FE> = Default::default();
        let mut base_receiver = BaseReceiver::<FE>::init_with_picked_delta(channel, pows.clone(), rng, delta)?;
        let base_voles_setup =
            base_receiver.receive(channel, compute_num_saved::<FE>(lpn_setup), rng)?;
        let delta = base_receiver.delta();

        let spsvole = SpsReceiver::<FE>::init(channel, pows, delta, rng)?;
        let seed = rng.gen::<Block>();
        let seed = scuttlebutt::cointoss::send(channel, &[seed])?[0];
        let lpn_rng = AesRng::from_seed(seed);
        let mut receiver = Self {
            lpn_setup,
            lpn_extend,
            spsvole,
            delta,
            base_voles: base_voles_setup,
            base_receiver,
            lpn_rng,
        };
        let mut base_voles_setup = Vec::new();
        receiver.receive_internal(channel, lpn_setup, 0, rng, &mut base_voles_setup)?;
        receiver.base_voles = base_voles_setup;
        // let mut base_voles_extend = Vec::new();
        // receiver.receive_internal(channel, LPN_SETUP_PARAMS, 0, rng, &mut base_voles_extend)?;
        // receiver.base_voles = base_voles_extend;
        Ok(receiver)
    }

    /// Init given a OT instance for spsvole and a picked delta
    pub fn init_with_picked_delta_and_ot<C: AbstractChannel, RNG: CryptoRng + Rng, FF: FiniteField>(
        channel: &mut C,
        rng: &mut RNG,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
        delta: FE,
        receiver: &Sender<FF>,
    ) -> Result<Self, Error> {
        let ot = receiver.extract_spsvole().extract_ot();
        let pows: Powers<FE> = Default::default();
        let mut base_receiver = BaseReceiver::<FE>::init_with_picked_delta_and_ot(channel, pows.clone(), rng, delta, ot)?;
        let base_voles_setup =
            base_receiver.receive(channel, compute_num_saved::<FE>(lpn_setup), rng)?;
        let delta = base_receiver.delta();

        let ot = receiver.extract_base_sender().extract_copee().extract_ot();
        let spsvole = SpsReceiver::<FE>::init_with_ot(channel, pows, delta, rng, ot)?;
        let seed = rng.gen::<Block>();
        let seed = scuttlebutt::cointoss::send(channel, &[seed])?[0];
        let lpn_rng = AesRng::from_seed(seed);
        let mut receiver = Self {
            lpn_setup,
            lpn_extend,
            spsvole,
            delta,
            base_voles: base_voles_setup,
            base_receiver,
            lpn_rng,
        };
        let mut base_voles_setup = Vec::new();
        receiver.receive_internal(channel, lpn_setup, 0, rng, &mut base_voles_setup)?;
        receiver.base_voles = base_voles_setup;
        // let mut base_voles_extend = Vec::new();
        // receiver.receive_internal(channel, LPN_SETUP_PARAMS, 0, rng, &mut base_voles_extend)?;
        // receiver.base_voles = base_voles_extend;
        Ok(receiver)
    }

    /// Init given a OT instance for spsvole and a picked delta
    pub fn init_with_picked_delta_and_ot_receiver<C: AbstractChannel, RNG: CryptoRng + Rng, FF: FiniteField>(
        channel: &mut C,
        rng: &mut RNG,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
        delta: FE,
        receiver: &Receiver<FF>,
    ) -> Result<Self, Error> {
        let ot = receiver.extract_base_receiver().extract_copee().extract_ot();
        let pows: Powers<FE> = Default::default();
        let mut base_receiver = BaseReceiver::<FE>::init_with_picked_delta_and_ot(channel, pows.clone(), rng, delta, ot)?;
        let base_voles_setup =
        base_receiver.receive(channel, compute_num_saved::<FE>(lpn_setup), rng)?;
        let delta = base_receiver.delta();
        
        let ot = receiver.extract_spsvole().extract_ot();
        let spsvole = SpsReceiver::<FE>::init_with_ot(channel, pows, delta, rng, ot)?;
        let seed = rng.gen::<Block>();
        let seed = scuttlebutt::cointoss::send(channel, &[seed])?[0];
        let lpn_rng = AesRng::from_seed(seed);
        let mut receiver = Self {
            lpn_setup,
            lpn_extend,
            spsvole,
            delta,
            base_voles: base_voles_setup,
            base_receiver,
            lpn_rng,
        };
        let mut base_voles_setup = Vec::new();
        receiver.receive_internal(channel, lpn_setup, 0, rng, &mut base_voles_setup)?;
        receiver.base_voles = base_voles_setup;
        // let mut base_voles_extend = Vec::new();
        // receiver.receive_internal(channel, LPN_SETUP_PARAMS, 0, rng, &mut base_voles_extend)?;
        // receiver.base_voles = base_voles_extend;
        Ok(receiver)
    }
}


impl<FE: FiniteField> SVoleReceiver for Receiver<FE> {
    type Msg = FE;

    fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
    ) -> Result<Self, Error> {
        let pows: Powers<FE> = Default::default();
        let mut base_receiver = BaseReceiver::<FE>::init(channel, pows.clone(), rng)?;
        let base_voles_setup =
            base_receiver.receive(channel, compute_num_saved::<FE>(lpn_setup), rng)?;
        let delta = base_receiver.delta();
        let spsvole = SpsReceiver::<FE>::init(channel, pows, delta, rng)?;
        let seed = rng.gen::<Block>();
        let seed = scuttlebutt::cointoss::send(channel, &[seed])?[0];
        let lpn_rng = AesRng::from_seed(seed);
        let mut receiver = Self {
            lpn_setup,
            lpn_extend,
            spsvole,
            delta,
            base_voles: base_voles_setup,
            base_receiver,
            lpn_rng,
        };
        let mut base_voles_setup = Vec::new();
        receiver.receive_internal(channel, lpn_setup, 0, rng, &mut base_voles_setup)?;
        receiver.base_voles = base_voles_setup;
        // let mut base_voles_extend = Vec::new();
        // receiver.receive_internal(channel, LPN_SETUP_PARAMS, 0, rng, &mut base_voles_extend)?;
        // receiver.base_voles = base_voles_extend;
        Ok(receiver)
    }    

    fn delta(&self) -> FE {
        self.delta
    }

    fn receive<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        output: &mut Vec<FE>,
    ) -> Result<(), Error> {
        self.receive_internal(
            channel,
            self.lpn_extend,
            compute_num_saved::<FE>(self.lpn_extend),
            rng,
            output,
        )
    }

    fn duplicate<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<Self, Error> {
        let mut base_voles = Vec::new();
        self.receive_internal(
            channel,
            self.lpn_setup,
            compute_num_saved::<FE>(self.lpn_setup),
            rng,
            &mut base_voles,
        )?;
        // let mut extras = Vec::new();
        // self.receive_internal(
        //     channel,
        //     LPN_SETUP_PARAMS,
        //     compute_num_saved::<FE>(LPN_SETUP_PARAMS),
        //     rng,
        //     &mut extras,
        // )?;
        // base_voles.extend(extras.into_iter());

        debug_assert!(base_voles.len() >= compute_num_saved::<FE>(self.lpn_extend));
        debug_assert!(self.base_voles.len() >= compute_num_saved::<FE>(self.lpn_extend));

        let spsvole = self.spsvole.duplicate(channel, rng)?;
        let base_receiver = self.base_receiver.clone();
        let lpn_rng = self.lpn_rng.fork();
        Ok(Self {
            lpn_setup: self.lpn_setup,
            lpn_extend: self.lpn_extend,
            spsvole,
            delta: self.delta,
            base_voles,
            base_receiver,
            lpn_rng,
        })
    }
}

impl<FF: FiniteField> SemiHonest for Sender<FF> {}
impl<FF: FiniteField> SemiHonest for Receiver<FF> {}
impl<FF: FiniteField> Malicious for Sender<FF> {}
impl<FF: FiniteField> Malicious for Receiver<FF> {}

impl<FE: FiniteField> Sender<FE> {
    /// Extracts the SPS Vole sender from the current sender.
    pub fn extract_spsvole(&self) -> SpsSender<FE> {
        return self.spsvole.clone();
    }

    /// Extracts the base VOLE sender from the current sender.
    pub fn extract_base_sender(&self) -> BaseSender<FE> {
        return self.base_sender.clone();
    }
}

impl<FE: FiniteField> Receiver<FE> {
    /// Extracts the SPS Vole sender from the current sender.
    pub fn extract_spsvole(&self) -> SpsReceiver<FE> {
        return self.spsvole.clone();
    }

    /// Extracts the base VOLE sender from the current sender.
    pub fn extract_base_receiver(&self) -> BaseReceiver<FE> {
        return self.base_receiver.clone();
    }
}



#[cfg(test)]
mod tests {
    use super::{Receiver, SVoleReceiver, SVoleSender, Sender, LPN_EXTEND_SMALL, LPN_SETUP_SMALL};
    use scuttlebutt::{
        field::{F128b, F40b, F61p, FiniteField as FF},
        AesRng, Channel,
    };
    use std::{
        io::{BufReader, BufWriter},
        os::unix::net::UnixStream,
    };

    fn test_lpn_svole_<FE: FF, Sender: SVoleSender<Msg = FE>, Receiver: SVoleReceiver<Msg = FE>>() {
        let (sender, receiver) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::new();
            let reader = BufReader::new(sender.try_clone().unwrap());
            let writer = BufWriter::new(sender);
            let mut channel = Channel::new(reader, writer);
            let mut vole =
                Sender::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
            let mut out = Vec::new();
            vole.send(&mut channel, &mut rng, &mut out).unwrap();
            out
        });
        let mut rng = AesRng::new();
        let reader = BufReader::new(receiver.try_clone().unwrap());
        let writer = BufWriter::new(receiver);
        let mut channel = Channel::new(reader, writer);
        let mut vole =
            Receiver::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
        let mut vs = Vec::new();
        vole.receive(&mut channel, &mut rng, &mut vs).unwrap();
        let uws = handle.join().unwrap();
        for i in 0..uws.len() as usize {
            let right = uws[i].0 * vole.delta() + vs[i];
            assert_eq!(uws[i].1, right);
        }
    }

    fn test_duplicate_svole_<
        FE: FF,
        Sender: SVoleSender<Msg = FE>,
        Receiver: SVoleReceiver<Msg = FE>,
    >() {
        let (sender, receiver) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::new();
            let reader = BufReader::new(sender.try_clone().unwrap());
            let writer = BufWriter::new(sender);
            let mut channel = Channel::new(reader, writer);
            let mut vole =
                Sender::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
            let mut uws = Vec::new();
            vole.send(&mut channel, &mut rng, &mut uws).unwrap();
            let mut vole2 = vole.duplicate(&mut channel, &mut rng).unwrap();
            let mut uws2 = Vec::new();
            vole2.send(&mut channel, &mut rng, &mut uws2).unwrap();
            let mut uws3 = Vec::new();
            vole.send(&mut channel, &mut rng, &mut uws3).unwrap();
            assert_ne!(uws2, uws3);
            uws.extend(uws2);
            uws.extend(uws3);
            uws
        });
        let mut rng = AesRng::new();
        let reader = BufReader::new(receiver.try_clone().unwrap());
        let writer = BufWriter::new(receiver);
        let mut channel = Channel::new(reader, writer);
        let mut vole =
            Receiver::init(&mut channel, &mut rng, LPN_SETUP_SMALL, LPN_EXTEND_SMALL).unwrap();
        let mut vs = Vec::new();
        vole.receive(&mut channel, &mut rng, &mut vs).unwrap();
        let mut vole2 = vole.duplicate(&mut channel, &mut rng).unwrap();
        let mut vs2 = Vec::new();
        vole2.receive(&mut channel, &mut rng, &mut vs2).unwrap();
        let mut vs3 = Vec::new();
        vole.receive(&mut channel, &mut rng, &mut vs3).unwrap();
        assert_ne!(vs2, vs3);
        vs.extend(vs2);
        vs.extend(vs3);

        let uws = handle.join().unwrap();
        for i in 0..uws.len() as usize {
            let right = uws[i].0 * vole.delta() + vs[i];
            assert_eq!(uws[i].1, right);
        }
    }

    #[test]
    fn test_lpn_svole_gf128() {
        test_lpn_svole_::<F128b, Sender<F128b>, Receiver<F128b>>();
    }

    #[test]
    fn test_lpn_svole_f61p() {
        test_lpn_svole_::<F61p, Sender<F61p>, Receiver<F61p>>();
    }

    #[test]
    fn test_lpn_svole_f40b() {
        test_lpn_svole_::<F40b, Sender<F40b>, Receiver<F40b>>();
    }

    #[test]
    fn test_duplicate_svole() {
        test_duplicate_svole_::<F61p, Sender<F61p>, Receiver<F61p>>();
    }

    #[test]
    fn test_duplicate_svole_f40b() {
        test_duplicate_svole_::<F40b, Sender<F40b>, Receiver<F40b>>();
    }
}
