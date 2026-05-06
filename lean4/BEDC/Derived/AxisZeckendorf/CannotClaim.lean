/-
CannotClaim registry for the AxisZeckendorf cluster. Each statement is a
deliberately negative theorem (or a True placeholder for a horizon claim
the cluster refuses to assert). These are the entries the paper-side
chapter `260_axis_zeckendorf_cannot_claim.tex` cites via `\notclaimed{…}`
inside per-chapter `closurestatus` blocks.
-/
import BEDC.Derived.AxisZeckendorf.Spine
import BEDC.Derived.AxisZeckendorf.Zeckendorf
import BEDC.Derived.AxisZeckendorf.Carry
import BEDC.Derived.AxisZeckendorf.FullAxis

namespace BEDC.Derived.AxisZeckendorf.CannotClaim

open BEDC.FKernel.Hist
open BEDC.Derived.AxisZeckendorf.Zeckendorf
open BEDC.Derived.AxisZeckendorf.Carry
open BEDC.Derived.AxisZeckendorf.FullAxis

theorem cannot_claim_011_is_infinity :
    ¬ hsame word_011 word_100 := zCarry_011_100_not_hsame

theorem cannot_claim_carry_is_hsame {h k : BHist} :
    ZCarry h k → ¬ hsame h k := zCarry_not_hsame

theorem cannot_claim_011_is_normal :
    ¬ ZNormal word_011 := znormal_word_011_absurd

theorem cannot_claim_boundary_01_in_zerospine :
    ¬ Spine.ZeroSpine boundary_01 := boundary_01_not_zeroSpine

theorem cannot_claim_dimLift_primitive_horizon : True := True.intro

theorem cannot_claim_fullAxis_is_real_horizon : True := True.intro

theorem cannot_claim_axisNat_replaces_natUp_horizon : True := True.intro

end BEDC.Derived.AxisZeckendorf.CannotClaim
