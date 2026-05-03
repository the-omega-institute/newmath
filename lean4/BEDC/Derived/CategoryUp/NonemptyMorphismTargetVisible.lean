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

end BEDC.Derived.CategoryUp
