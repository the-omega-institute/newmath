import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_nonempty_morphism_target_visible {source target morph : BHist} :
    CategoryHomCarrier source target morph -> (hsame morph BHist.Empty -> False) ->
      exists k r : BHist, morph = BHist.e1 k /\ target = BHist.e1 r /\
        UnaryHistory k /\ UnaryHistory r /\ Cont source k r := by
  intro homCarrier nonempty
  cases morph with
  | Empty =>
      exact False.elim (nonempty (hsame_refl BHist.Empty))
  | e0 k =>
      exact False.elim (unary_no_zero_extension homCarrier.right.right.left)
  | e1 k =>
      cases target with
      | Empty =>
          cases homCarrier.right.right.right
      | e0 r =>
          cases homCarrier.right.right.right
      | e1 r =>
          exact Exists.intro k
            (Exists.intro r
              (And.intro rfl
                (And.intro rfl
                  (And.intro (unary_e1_inversion homCarrier.right.right.left)
                    (And.intro (unary_e1_inversion homCarrier.right.left)
                      (BHist.e1.inj homCarrier.right.right.right))))))

theorem CategoryHomCarrier_nonempty_morphism_visible_endpoint_cases {source target morph : BHist} :
    CategoryHomCarrier source target morph -> (hsame morph BHist.Empty -> False) ->
      (∃ r : BHist, source = BHist.Empty ∧ target = BHist.e1 r ∧ morph = BHist.e1 r ∧
        UnaryHistory r) ∨
        (∃ a k r : BHist, source = BHist.e1 a ∧ morph = BHist.e1 k ∧
          target = BHist.e1 r ∧ UnaryHistory a ∧ UnaryHistory k ∧ UnaryHistory r ∧
            Cont (BHist.e1 a) k r) := by
  intro homCarrier nonempty
  cases source with
  | Empty =>
      left
      have sourceData := CategoryHomCarrier_empty_source_iff.mp homCarrier
      cases target with
      | Empty =>
          exact False.elim (nonempty sourceData.right)
      | e0 r =>
          exact False.elim (unary_no_zero_extension sourceData.left)
      | e1 r =>
          cases sourceData.right
          exact Exists.intro r
            (And.intro rfl
              (And.intro rfl (And.intro rfl (unary_e1_inversion sourceData.left))))
  | e0 a =>
      exact False.elim (unary_no_zero_extension homCarrier.left)
  | e1 a =>
      right
      cases morph with
      | Empty =>
          exact False.elim (nonempty (hsame_refl BHist.Empty))
      | e0 k =>
          exact False.elim (unary_no_zero_extension homCarrier.right.right.left)
      | e1 k =>
          cases target with
          | Empty =>
              cases homCarrier.right.right.right
          | e0 r =>
              cases homCarrier.right.right.right
          | e1 r =>
              exact Exists.intro a
                (Exists.intro k
                  (Exists.intro r
                    (And.intro rfl
                      (And.intro rfl
                        (And.intro rfl
                          (And.intro (unary_e1_inversion homCarrier.left)
                            (And.intro (unary_e1_inversion homCarrier.right.right.left)
                              (And.intro (unary_e1_inversion homCarrier.right.left)
                                (BHist.e1.inj homCarrier.right.right.right)))))))))

end BEDC.Derived.CategoryUp
