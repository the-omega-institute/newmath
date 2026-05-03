import BEDC.Derived.CategoryUp.EmptyComposite
import BEDC.Derived.CategoryUp.CompositeEmptyTail

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuationMorphism_comp_tail_nonempty_cases {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    (hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty -> False) ->
      (hsame left.tail BHist.Empty -> False) ∨
        (hsame right.tail BHist.Empty -> False) := by
  intro compositeNonempty
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          cases leftTail with
          | Empty =>
              right
              intro rightEmpty
              apply compositeNonempty
              cases rightEmpty
              exact hsame_refl BHist.Empty
          | e0 leftTail =>
              left
              intro leftEmpty
              exact not_hsame_e0_empty leftEmpty
          | e1 leftTail =>
              left
              intro leftEmpty
              exact not_hsame_e1_empty leftEmpty

theorem CategoryHomCarrier_comp_result_nonempty_cases {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (hsame fg BHist.Empty -> False) ->
        (hsame f BHist.Empty -> False) ∨ (hsame g BHist.Empty -> False) := by
  intro left right comp resultNonempty
  cases f with
  | Empty =>
      right
      intro gEmpty
      apply resultNonempty
      cases gEmpty
      cases comp
      exact hsame_refl BHist.Empty
  | e0 fTail =>
      left
      intro fEmpty
      exact not_hsame_e0_empty fEmpty
  | e1 fTail =>
      left
      intro fEmpty
      exact not_hsame_e1_empty fEmpty

end BEDC.Derived.CategoryUp
