import BEDC.Derived.ComplexDifferentiabilityUp

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.ComplexDiffUp

theorem CplxDiffAt_seed_boundary_surface {f z fp : BHist} :
    CplxDiffAt f z fp ->
      CplxDiffLedgerPolicy f z fp ∧ CplxDiffSourceSpec f z fp ∧
        ∃ h : BHist, ∃ q : BHist,
          CplxDiffQuot f z h q ∧ Cont f h q ∧ CplxNonZero h ∧ CplxNonZero q ∧
            hsame q fp := by
  intro diff
  exact And.intro (CplxDiffLedgerPolicy_of_diff diff)
    (And.intro (CplxDiffSourceSpec_of_diff diff) (CplxDiffAt_witness_nonzero_result diff))

end BEDC.Derived.ComplexDifferentiabilityUp
