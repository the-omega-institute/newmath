import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist

theorem ContinuationMorphism_tail_nonempty_shape_cases {a b : BHist}
    (m : ContinuationMorphism a b) :
    (hsame m.tail BHist.Empty -> False) ->
      (∃ t : BHist, m.tail = BHist.e0 t) ∨ (∃ t : BHist, m.tail = BHist.e1 t) := by
  intro tailNonempty
  cases m with
  | mk tail rel =>
      cases tail with
      | Empty =>
          exact False.elim (tailNonempty (hsame_refl BHist.Empty))
      | e0 tail =>
          left
          exact Exists.intro tail rfl
      | e1 tail =>
          right
          exact Exists.intro tail rfl

end BEDC.Derived.CategoryUp
