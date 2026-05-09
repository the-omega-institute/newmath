import BEDC.Derived.ComplexDifferentiabilityUp.SourceObligationSurface

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp

theorem ComplexDiffSeed_boundary {f z fp pattern : BHist} :
    CplxDiffAt f z fp ->
      CplxDiffPatternSpec f z pattern ->
        CplxDiffSourceSpec f z fp ∧ CplxDiffLedgerPolicy f z fp ∧
          (∃ h : BHist, ∃ q : BHist,
            CplxDiffQuot f z h q ∧ Cont h q pattern ∧ UnaryHistory h ∧
              UnaryHistory q) ∧
            SemanticNameCert (CplxDiffAt f z) (CplxDiffAt f z) (CplxDiffAt f z)
              hsame := by
  intro diff patternSpec
  exact And.intro (CplxDiffSourceSpec_of_diff diff)
    (And.intro (CplxDiffLedgerPolicy_of_diff diff)
      (And.intro (CplxDiffPatternSpec_witness_readback patternSpec)
        (complex_diff_semantic_name_certificate diff)))

end BEDC.Derived.ComplexDifferentiabilityUp
