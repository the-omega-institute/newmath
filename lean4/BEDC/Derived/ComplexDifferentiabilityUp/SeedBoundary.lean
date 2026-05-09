import BEDC.Derived.ComplexDifferentiabilityUp

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.Derived.ComplexDiffUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ComplexDifferentiabilitySeed_boundary {f z fp : BHist} :
    CplxDiffAt f z fp ->
      CplxDiffLedgerPolicy f z fp ∧
        SemanticNameCert (CplxDiffAt f z) (CplxDiffAt f z) (CplxDiffAt f z) hsame ∧
          ∃ h : BHist, ∃ q : BHist,
            CplxDiffQuot f z h q ∧ Cont f h q ∧ CplxNonZero h ∧ CplxNonZero q ∧
              hsame q fp := by
  intro diff
  exact And.intro (CplxDiffLedgerPolicy_of_diff diff)
    (And.intro (complex_diff_semantic_name_certificate diff)
      (CplxDiffAt_witness_nonzero_result diff))

end BEDC.Derived.ComplexDifferentiabilityUp
