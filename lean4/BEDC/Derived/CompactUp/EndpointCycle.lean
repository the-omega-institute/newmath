import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CompactNetWitness_endpoint_cycle_precision_empty {center precision net : BHist} :
    CompactNetWitness center precision net -> hsame center net -> hsame precision BHist.Empty := by
  intro witness sameEndpoint
  exact cont_right_unit_unique
    (cont_result_hsame_transport witness.right.right.right (hsame_symm sameEndpoint))

end BEDC.Derived.CompactUp
