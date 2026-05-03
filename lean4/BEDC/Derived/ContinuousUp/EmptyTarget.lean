import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusWitness_empty_target_iff {source modulus : BHist} :
    ContinuousModulusWitness source modulus BHist.Empty ↔
      hsame source BHist.Empty ∧ hsame modulus BHist.Empty := by
  constructor
  · intro witness
    have split := cont_empty_result_inversion witness.right.right.right
    exact And.intro split.left split.right
  · intro endpoints
    cases endpoints.left
    cases endpoints.right
    exact And.intro unary_empty
      (And.intro unary_empty (And.intro unary_empty (cont_intro rfl)))

end BEDC.Derived.ContinuousUp
