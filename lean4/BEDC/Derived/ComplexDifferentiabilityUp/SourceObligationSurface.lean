import BEDC.Derived.ComplexDifferentiabilityUp

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp
open BEDC.Derived.ComplexUp

theorem CplxDiffAt_source_obligation_surface {f z fp : BHist} :
    CplxDiffAt f z fp ->
      CplxDiffSourceSpec f z fp ∧ ComplexHistoryCarrier fp ∧
        exists h : BHist, exists q : BHist,
          CplxNonZero h ∧ UnaryHistory h ∧ UnaryHistory q ∧ CplxDiffQuot f z h q ∧
            Cont f h q ∧ hsame q fp := by
  intro diff
  exact And.intro (CplxDiffSourceSpec_of_diff diff)
    (And.intro diff.right.right.left (CplxDiffAt_witness_nonzero_unary_step diff))

end BEDC.Derived.ComplexDifferentiabilityUp
