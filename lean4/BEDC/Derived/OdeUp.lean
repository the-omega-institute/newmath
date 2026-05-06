import BEDC.FKernel.Cont

namespace BEDC.Derived.OdeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def OdeLocalFlowRow (t0 x0 t1 x1 v p ell : BHist) : Prop :=
  Cont t0 x0 p ∧ Cont p v ell ∧ Cont t1 ell x1

theorem OdeLocalFlowRow_picard_continuation_scope
    {t0 x0 t1 x1 v p ell next route : BHist} :
    OdeLocalFlowRow t0 x0 t1 x1 v p ell -> Cont x1 next route ->
      exists carried : BHist, Cont ell next carried ∧ Cont t1 carried route := by
  intro row endpoint
  exact cont_assoc_left_exists row.right.right endpoint

end BEDC.Derived.OdeUp
