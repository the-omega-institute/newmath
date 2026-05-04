import BEDC.Derived.FunctorUp
import BEDC.Derived.CategoryUp.CompResultNonemptySourceTargetCases

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_nonempty_result_target_visible {p a b c f g k : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g (BHist.e1 k) ->
        ∃ r : BHist, append p c = BHist.e1 r ∧ UnaryHistory k ∧ UnaryHistory r ∧
          Cont (append p a) (BHist.e1 k) (BHist.e1 r) := by
  intro left right comp
  have casesData :=
    CategoryHomCarrier_comp_result_nonempty_source_target_cases left right comp
      (fun sameEmpty => not_hsame_e1_empty sameEmpty)
  cases casesData with
  | inl emptySource =>
      cases emptySource.right with
      | intro k' targetData =>
          cases targetData with
          | intro r data =>
              cases data.left
              exact Exists.intro r data.right
  | inr visibleSource =>
      cases visibleSource with
      | intro s sourceData =>
          cases sourceData with
          | intro k' targetData =>
              cases targetData with
              | intro r data =>
                  cases data.right.left
                  have sourceSame : hsame (BHist.e1 s) (append p a) := by
                    exact data.left.symm
                  have sourceRel : Cont (append p a) (BHist.e1 k) (BHist.e1 r) :=
                    cont_hsame_transport sourceSame (hsame_refl (BHist.e1 k))
                      (hsame_refl (BHist.e1 r)) data.right.right.right.right.right.right
                  exact Exists.intro r
                    (And.intro data.right.right.left
                      (And.intro data.right.right.right.right.left
                        (And.intro data.right.right.right.right.right.left sourceRel)))

theorem FunctorPrefixHomCarrier_comp_nonempty_result_source_target_cases
    {p a b c f g k : BHist} :
    CategoryHomCarrier (append p a) (append p b) f ->
      CategoryHomCarrier (append p b) (append p c) g -> Cont f g (BHist.e1 k) ->
        (hsame (append p a) BHist.Empty ∧ ∃ r : BHist, append p c = BHist.e1 r ∧
            UnaryHistory k ∧ UnaryHistory r ∧
              Cont (append p a) (BHist.e1 k) (BHist.e1 r)) ∨
          (∃ s r : BHist, append p a = BHist.e1 s ∧ append p c = BHist.e1 r ∧
            UnaryHistory s ∧ UnaryHistory k ∧ UnaryHistory r ∧
              Cont (BHist.e1 s) (BHist.e1 k) (BHist.e1 r)) := by
  intro left right comp
  have casesData :=
    CategoryHomCarrier_comp_result_nonempty_source_target_cases left right comp
      (fun sameEmpty => not_hsame_e1_empty sameEmpty)
  cases casesData with
  | inl emptySource =>
      left
      cases emptySource.right with
      | intro k' targetData =>
          cases targetData with
          | intro r data =>
              cases data.left
              exact And.intro emptySource.left (Exists.intro r data.right)
  | inr visibleSource =>
      right
      cases visibleSource with
      | intro s sourceData =>
          cases sourceData with
          | intro k' targetData =>
              cases targetData with
              | intro r data =>
                  cases data.right.left
                  exact Exists.intro s
                    (Exists.intro r
                      (And.intro data.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro data.right.right.right.right.right.left
                                data.right.right.right.right.right.right))))))

end BEDC.Derived.FunctorUp
