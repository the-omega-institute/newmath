import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CompactNetWitness_empty_net_iff {center precision : BHist} :
    CompactNetWitness center precision BHist.Empty ↔
      hsame center BHist.Empty ∧ hsame precision BHist.Empty := by
  constructor
  · intro witness
    have split := cont_empty_result_inversion witness.right.right.right
    exact And.intro split.left split.right
  · intro endpoints
    cases endpoints.left
    cases endpoints.right
    exact And.intro unary_empty
      (And.intro unary_empty (And.intro unary_empty (cont_intro rfl)))

end BEDC.Derived.CompactUp
