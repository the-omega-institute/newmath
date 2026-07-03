import BEDC.Derived.RHRoute.StripRationalKit

/-!
Window lower-bound infrastructure for the strip first-zeros Herglotz bound,
built on the propext-free BEDC `RationalUp` rational (same foundation as
`IntervalMatrixPSD` / `StripArchimedeanBound`), NOT on native-`Int` `RatInterval`
(whose order lemmas carry `propext`).

Core reusable fact `htermMinus_lb`: on a panel `[lo,hi]` where the square is
bounded by `M`, a single Herglotz kernel term `aa / (aa^2 + (t-g)^2)` is bounded
below by `aa / (aa^2 + M)` — a direct application of the denominator antitone
lemma `ratDivApart_le_same_num_den_mono`.  Summed over the 29 zero ordinates and
swept over a subdivision this yields `K29 t ≥ 167/1000` on `[17,18]` (separate
steps).  Not RH.
-/

namespace BEDC.Derived.RHRoute.StripFirstZerosK29Window

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.StripRationalKit

abbrev Rat : Type := BEDC.Derived.RationalUp.RatNum

/-- Herglotz numerator `a = 4/5` (`= 2*(sigma - 1/2)` with `sigma = 13/10`). -/
def aa : Rat := qq 4 5

theorem aa_pos : ratLt ratZero aa := by
  unfold aa qq StripExclusionAssembly.q
  exact BEDC.Derived.RationalOrderArithUp.div_pos
    (natRat_pos_of_pos (by decide)) (natRat_pos_of_pos (by decide))

theorem aa_nonneg : ratLe ratZero aa :=
  ratLt_to_ratLe aa_pos

/-- Square of a real is nonneg (Herglotz panel numerators are squares). -/
theorem sq_nonneg (u : Rat) : ratLe ratZero (ratMul u u) :=
  BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg u

/-- **Per-term interval lower bound.**  Given the two panel denominators are
positive and the panel square bound `(t-g)^2 ≤ M`, the Herglotz term
`aa / (aa^2 + (t-g)^2)` is at least `aa / (aa^2 + M)`. -/
theorem htermMinus_lb {g t M : Rat}
    (hdenMinusPos :
      ratLt ratZero (ratAdd (ratMul aa aa) (ratMul (ratSub t g) (ratSub t g))))
    (hdenMPos : ratLt ratZero (ratAdd (ratMul aa aa) M))
    (hsq : ratLe (ratMul (ratSub t g) (ratSub t g)) M) :
    ratLe
      (ratDivApart aa (ratAdd (ratMul aa aa) M) (ratApart0_of_pos hdenMPos))
      (ratDivApart aa
        (ratAdd (ratMul aa aa) (ratMul (ratSub t g) (ratSub t g)))
        (ratApart0_of_pos hdenMinusPos)) := by
  have hdenLe :
      ratLe (ratAdd (ratMul aa aa) (ratMul (ratSub t g) (ratSub t g)))
        (ratAdd (ratMul aa aa) M) :=
    BEDC.Derived.LocatedReal.ratLe_add_left_mono (x := ratMul aa aa) hsq
  exact ratDivApart_le_same_num_den_mono
    aa_nonneg hdenMinusPos hdenMPos
    (ratApart0_of_pos hdenMinusPos) (ratApart0_of_pos hdenMPos) hdenLe

end BEDC.Derived.RHRoute.StripFirstZerosK29Window
