import BEDC.FKernel.Cont
import BEDC.Derived.CategoryUp.EmptyComposite
import BEDC.Derived.CategoryUp.CompositeEmptyTail

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

theorem ContinuationMorphism_comp_tail_nonempty_endpoint_cases {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    (hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty -> False) ->
      (hsame a b -> False) ∨ (hsame b c -> False) := by
  intro compositeNonempty
  have tailCases :=
    ContinuationMorphism_comp_tail_nonempty_cases left right compositeNonempty
  cases tailCases with
  | inl leftTailNonempty =>
      left
      intro sameAB
      exact leftTailNonempty ((ContinuationMorphism_tail_empty_endpoint_hsame_iff left).mpr sameAB)
  | inr rightTailNonempty =>
      right
      intro sameBC
      exact rightTailNonempty
        ((ContinuationMorphism_tail_empty_endpoint_hsame_iff right).mpr sameBC)

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

theorem CategoryHomCarrier_comp_result_nonempty_endpoint_cases {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (hsame fg BHist.Empty -> False) ->
        (hsame a b -> False) \/ (hsame b c -> False) := by
  intro left right comp resultNonempty
  have factorCases :=
    CategoryHomCarrier_comp_result_nonempty_cases left right comp resultNonempty
  cases factorCases with
  | inl leftNonempty =>
      left
      intro sameAB
      have leftEndomorphism : CategoryHomCarrier a a f :=
        CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_symm sameAB)
          (hsame_refl f) left
      exact leftNonempty (CategoryHomCarrier_endomorphism_empty_iff.mp leftEndomorphism).right
  | inr rightNonempty =>
      right
      intro sameBC
      have rightEndomorphism : CategoryHomCarrier b b g :=
        CategoryHomCarrier_hsame_transport (hsame_refl b) (hsame_symm sameBC)
          (hsame_refl g) right
      exact rightNonempty (CategoryHomCarrier_endomorphism_empty_iff.mp rightEndomorphism).right

theorem CategoryHomCarrier_comp_result_nonempty_iff {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      ((hsame fg BHist.Empty -> False) <->
        (hsame f BHist.Empty -> False) ∨ (hsame g BHist.Empty -> False)) := by
  intro left right comp
  cases comp
  exact BEDC.FKernel.Cont.append_nonempty_iff

theorem CategoryHomCarrier_comp_result_nonempty_target_visible {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (hsame fg BHist.Empty -> False) ->
        ∃ k r : BHist, fg = BHist.e1 k ∧ c = BHist.e1 r ∧
          UnaryHistory k ∧ UnaryHistory r ∧ Cont a (BHist.e1 k) (BHist.e1 r) := by
  intro left right comp resultNonempty
  have composite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  cases fg with
  | Empty =>
      exact False.elim (resultNonempty (hsame_refl BHist.Empty))
  | e0 k =>
      exact False.elim (unary_no_zero_extension composite.right.right.left)
  | e1 k =>
      cases c with
      | Empty =>
          cases composite.right.right.right
      | e0 r =>
          cases composite.right.right.right
      | e1 r =>
          exact Exists.intro k
            (Exists.intro r
              (And.intro rfl
                (And.intro rfl
                  (And.intro (unary_e1_inversion composite.right.right.left)
                    (And.intro (unary_e1_inversion composite.right.left)
                      composite.right.right.right)))))

end BEDC.Derived.CategoryUp
