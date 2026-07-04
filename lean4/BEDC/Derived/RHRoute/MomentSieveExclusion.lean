import BEDC.Derived.RHRoute.StripRationalKit
import BEDC.Derived.RationalSquareOrderUp

/-!
Finite moment-sieve first-contact exclusion (propext-free, BEDC `RationalUp` Rat).

Formalises the certificate mechanism of the heat-flow / moment-sandwich route
(session 6a4266c5): a "first contact" of the heat flow `U(h,T)` requires
`U = 0`, `U_T = 0`, `U_TT ≥ 0` simultaneously.  Each of `U, U_T, U_TT` is
bracketed by finite alternating Taylor truncations of its moment series,
`L^{(j)} ≤ · ≤ R^{(j)}`.  A single rational witness — one truncation with the
wrong sign — kills the contact at that point.  The finite sign checks are the
formalised content; the analytic bracketing `L ≤ U ≤ R` is the hypothesis (the
honest ceiling, exactly as with the strip explicit-formula identity).  The
large-`T` closure needed for the actual zeta kernel is a high-frequency
positivity bound = RH content, NOT provided here.  Not RH.
-/

namespace BEDC.Derived.RHRoute.MomentSieveExclusion

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.StripRationalKit

abbrev Rat : Type := BEDC.Derived.RationalUp.RatNum

private theorem ratLt_le_trans_local {x y z : Rat}
    (hxy : ratLt x y) (hyz : ratLe y z) : ratLt x z := by
  apply ratLe_not_le_to_ratLt
  · exact ratLe_trans (ratLt_to_ratLe hxy) hyz
  · intro zx
    exact ratLt_not_ratLe_reverse hxy (ratLe_trans hyz zx)

/-- The finite data certifying no first contact at one point via a positive lower
truncation: the Taylor lower bracket of `U` plus its positive sign. -/
structure ContactCellWitness where
  U0 : Rat
  L0 : Rat
  bracket_lo : ratLe L0 U0        -- L0 ≤ U  (analytic Taylor lower bound; hypothesis)
  lower_pos  : ratLt ratZero L0   -- 0 < L0  (finite rational sign check; the witness)

/-- **First-contact exclusion.**  A positive lower truncation forces `U > 0`, so
`U = 0` is impossible — no first contact at this point. -/
theorem no_first_contact (w : ContactCellWitness) : ratLt ratZero w.U0 :=
  ratLt_le_trans_local w.lower_pos w.bracket_lo

theorem heat_value_ne_zero (w : ContactCellWitness) : ¬ RatEq w.U0 ratZero := by
  intro hEq
  exact BEDC.Derived.RationalSquareOrderUp.ratLt_irrefl ratZero
    (BEDC.Real.RatNumKernel.ratLt_of_RatEq_right (no_first_contact w) hEq)

/-- Symmetric witness via a negative upper truncation `R0 < 0 ⟹ U < 0`. -/
structure ContactCellWitnessNeg where
  U0 : Rat
  R0 : Rat
  bracket_hi : ratLe U0 R0        -- U ≤ R0
  upper_neg  : ratLt R0 ratZero   -- R0 < 0

theorem no_first_contact_neg (w : ContactCellWitnessNeg) : ratLt w.U0 ratZero :=
  BEDC.Derived.RationalUp.ratLe_lt_trans w.bracket_hi w.upper_neg

end BEDC.Derived.RHRoute.MomentSieveExclusion
