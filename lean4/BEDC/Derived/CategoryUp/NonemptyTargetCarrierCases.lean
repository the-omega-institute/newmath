import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp
open BEDC.FKernel.Hist BEDC.FKernel.Cont BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_nonempty_morphism_target_carrier_cases
    {a target morph : BHist} :
    CategoryHomCarrier (BHist.e1 a) target morph -> (hsame morph BHist.Empty -> False) ->
      exists k r : BHist, morph = BHist.e1 k /\ target = BHist.e1 r /\
        CategoryHomCarrier (BHist.e1 a) r k := by
  intro homCarrier nonempty
  cases CategoryHomCarrier_e1_source_nonempty_morphism_target_cases homCarrier nonempty with
  | intro k visibleCase =>
      cases visibleCase with
      | intro r data =>
          exact Exists.intro k
            (Exists.intro r
              (And.intro data.left
                (And.intro data.right.left
                  (And.intro (unary_e1_closed data.right.right.left)
                    (And.intro data.right.right.right.right.left
                      (And.intro data.right.right.right.left
                        data.right.right.right.right.right))))))

end BEDC.Derived.CategoryUp
