import BEDC.Derived.CategoryUp.NonemptyMorphismSourceCases

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_nonempty_morphism_endpoint_cases {source target morph : BHist} :
    CategoryHomCarrier source target morph -> (hsame morph BHist.Empty -> False) ->
      (source = BHist.Empty ∧ ∃ k : BHist,
        morph = BHist.e1 k ∧ target = BHist.e1 k ∧ UnaryHistory k) ∨
        (∃ a k r : BHist, source = BHist.e1 a ∧ morph = BHist.e1 k ∧
          target = BHist.e1 r ∧ UnaryHistory a ∧ UnaryHistory k ∧ UnaryHistory r ∧
            Cont (BHist.e1 a) (BHist.e1 k) (BHist.e1 r)) := by
  intro homCarrier nonempty
  cases CategoryHomCarrier_nonempty_morphism_source_cases homCarrier nonempty with
  | inl emptyCase =>
      left
      cases emptyCase with
      | intro sourceEq targetData =>
          cases sourceEq
          cases morph with
          | Empty =>
              exact False.elim (nonempty (hsame_refl BHist.Empty))
          | e0 k =>
              exact False.elim (unary_no_zero_extension homCarrier.right.right.left)
          | e1 k =>
              cases targetData.right
              exact And.intro rfl
                (Exists.intro k
                  (And.intro rfl
                    (And.intro rfl (unary_e1_inversion targetData.left))))
  | inr visibleCase =>
      right
      cases visibleCase with
      | intro a data =>
          cases data with
          | intro k data =>
              cases data with
              | intro r fields =>
                  exact Exists.intro a
                    (Exists.intro k
                      (Exists.intro r
                        (And.intro fields.left
                          (And.intro fields.right.left
                            (And.intro fields.right.right.left
                              (And.intro fields.right.right.right.left
                                (And.intro fields.right.right.right.right.left
                                  (And.intro fields.right.right.right.right.right.left
                                    (cont_step_one
                                      fields.right.right.right.right.right.right)))))))))

end BEDC.Derived.CategoryUp
