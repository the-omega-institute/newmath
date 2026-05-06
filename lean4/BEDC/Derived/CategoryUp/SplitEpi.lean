import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist BEDC.FKernel.Cont BEDC.FKernel.Unary

theorem CategorySplitEpiWitness_right_cancellative {a b x f s sf u v fu fv : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b a s -> Cont s f sf ->
      hsame sf BHist.Empty -> CategoryHomCarrier b x u -> CategoryHomCarrier b x v ->
        Cont f u fu -> Cont f v fv -> hsame fu fv -> hsame u v := by
  intro _ _ splitComposite splitEmpty _ _ leftComposite rightComposite sameComposite
  cases splitComposite
  have fEmpty : f = BHist.Empty := (append_eq_empty_iff.mp splitEmpty).right
  cases fEmpty
  cases leftComposite
  cases rightComposite
  exact (append_empty_left u).symm.trans (sameComposite.trans (append_empty_left v))

end BEDC.Derived.CategoryUp
