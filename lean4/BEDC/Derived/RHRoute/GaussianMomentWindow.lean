import BEDC.Derived.RHRoute.MomentSieveExclusion

/-!
Complete finite bounded-`T` moment-sieve certificate on the Gaussian solvable
model (session 6a4266c5).  For `C_G(t)=e^{-t²}` at `h=0`, the sign-relevant
`N=1` lower truncation reduces to the rational polynomial in `x = T²`,
`P(x) := 384 - 96x + 12x² - x³` (= `384 · L0_reduced`).

The SOS factorization `P(x) = 24 + (6-x)(51 + (x-3)²)` (verified numerically)
gives, for `x ∈ [0,6]` (so `T ∈ [0,√6]`), `P(x) ≥ 24 > 0`: the lower truncation
is strictly positive on the whole bounded-`T` window, so — via the moment-sieve
first-contact mechanism with the Taylor bracket — the heat flow is `> 0`, no
first contact.  The finite `A`-part, fully closed on the solvable model; the
large-`T` closure for the actual zeta kernel is RH content.  Not RH.

The degree-3 factorization identity is taken as an explicit hypothesis (it needs
a fast propext-free polynomial ring-identity normalizer over BEDC Rat; the
framework's `AlgebraNormalize` one is private).  The interval positivity and
no-contact conclusion are proven unconditionally.
-/

namespace BEDC.Derived.RHRoute.GaussianMomentWindow

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

/-- `P(x) = 384 - 96x + 12x² - x³` (= `384 · L0_reduced` at `h=0`). -/
def Pval (x : Rat) : Rat :=
  ratSub
    (ratAdd (ratSub (natRat 384) (ratMul (natRat 96) x))
      (ratMul (natRat 12) (ratMul x x)))
    (ratMul x (ratMul x x))

/-- The strictly-positive core `51 + (x-3)²`. -/
def core (x : Rat) : Rat :=
  ratAdd (natRat 51) (ratMul (ratSub x (natRat 3)) (ratSub x (natRat 3)))

theorem core_pos (x : Rat) : ratLt ratZero (core x) := by
  unfold core
  have hsq : ratLe ratZero (ratMul (ratSub x (natRat 3)) (ratSub x (natRat 3))) :=
    BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg (ratSub x (natRat 3))
  have hle : ratLe (natRat 51)
      (ratAdd (natRat 51) (ratMul (ratSub x (natRat 3)) (ratSub x (natRat 3)))) :=
    BEDC.Real.RatNumLogEnclosure.ratLe_add_nonneg_right (natRat 51)
      (ratMul (ratSub x (natRat 3)) (ratSub x (natRat 3))) hsq
  exact ratLt_le_trans_local (natRat_pos_of_pos (by decide)) hle

/-- **Window positivity.**  Given the SOS factorization, `P(x) > 0` for `x ∈ [0,6]`. -/
theorem Pval_pos_on_window (x : Rat)
    (hid : RatEq (Pval x)
      (ratAdd (natRat 24) (ratMul (ratSub (natRat 6) x) (core x))))
    (hx0 : ratLe ratZero x) (hx6 : ratLe x (natRat 6)) :
    ratLt ratZero (Pval x) := by
  have h6x : ratLe ratZero (ratSub (natRat 6) x) :=
    BEDC.Derived.RationalUp.ratSub_nonneg_of_le hx6
  have hprod : ratLe ratZero (ratMul (ratSub (natRat 6) x) (core x)) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg h6x (ratLt_to_ratLe (core_pos x))
  have hle : ratLe (natRat 24)
      (ratAdd (natRat 24) (ratMul (ratSub (natRat 6) x) (core x))) :=
    BEDC.Real.RatNumLogEnclosure.ratLe_add_nonneg_right (natRat 24)
      (ratMul (ratSub (natRat 6) x) (core x)) hprod
  have hpos : ratLt ratZero
      (ratAdd (natRat 24) (ratMul (ratSub (natRat 6) x) (core x))) :=
    ratLt_le_trans_local (natRat_pos_of_pos (by decide)) hle
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right hpos (RatEq_symm hid)

/-- **No first contact on the bounded-T window.**  With the Taylor lower bracket
`Pval x ≤ 384·U` supplied, positivity of `P` forbids `U = 0`. -/
theorem no_contact_on_window (x scaledU : Rat)
    (hid : RatEq (Pval x)
      (ratAdd (natRat 24) (ratMul (ratSub (natRat 6) x) (core x))))
    (hx0 : ratLe ratZero x) (hx6 : ratLe x (natRat 6))
    (hbracket : ratLe (Pval x) scaledU) :
    ratLt ratZero scaledU :=
  ratLt_le_trans_local (Pval_pos_on_window x hid hx0 hx6) hbracket

end BEDC.Derived.RHRoute.GaussianMomentWindow
