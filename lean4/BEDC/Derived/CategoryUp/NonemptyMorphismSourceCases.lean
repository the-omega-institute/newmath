import BEDC.Derived.CategoryUp.TargetCases

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_nonempty_morphism_source_cases {source target morph : BHist} :
    CategoryHomCarrier source target morph ->
      (hsame morph BHist.Empty -> False) ->
        (source = BHist.Empty ∧ UnaryHistory target ∧ hsame morph target) ∨
          (exists a k r : BHist,
            source = BHist.e1 a ∧ morph = BHist.e1 k ∧ target = BHist.e1 r ∧
              UnaryHistory a ∧ UnaryHistory k ∧ UnaryHistory r ∧
                Cont (BHist.e1 a) k r) := by
  intro homCarrier nonempty
  cases source with
  | Empty =>
      left
      have emptySource :=
        (CategoryHomCarrier_empty_source_iff (b := target) (f := morph)).mp homCarrier
      exact And.intro rfl (And.intro emptySource.left emptySource.right)
  | e0 a =>
      exact False.elim (CategoryHomCarrier_e0_source_absurd homCarrier)
  | e1 a =>
      cases morph with
      | Empty =>
          exact False.elim (nonempty (hsame_refl BHist.Empty))
      | e0 k =>
          exact False.elim (unary_no_zero_extension homCarrier.right.right.left)
      | e1 k =>
          right
          have targetCases := CategoryHomCarrier_e1_morphism_target_cases homCarrier
          cases targetCases with
          | intro r targetData =>
              cases targetData with
              | intro targetEq tailCarrier =>
                  exact Exists.intro a
                    (Exists.intro k
                      (Exists.intro r
                        (And.intro rfl
                          (And.intro rfl
                            (And.intro targetEq
                              (And.intro (unary_e1_inversion tailCarrier.left)
                                (And.intro tailCarrier.right.right.left
                                  (And.intro tailCarrier.right.left
                                    tailCarrier.right.right.right))))))))

end BEDC.Derived.CategoryUp
