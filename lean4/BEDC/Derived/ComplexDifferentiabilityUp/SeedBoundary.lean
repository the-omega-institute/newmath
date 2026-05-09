import BEDC.Derived.ComplexDifferentiabilityUp.ObligationSurface
import BEDC.Derived.ComplexDifferentiabilityUp.SourceObligationSurface

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp
open BEDC.Derived.ComplexUp

theorem CplxDiffSeedBoundary_surface {f z fp pattern : BHist} :
    CplxDiffAt f z fp ->
      CplxDiffPatternSpec f z pattern ->
        CplxDiffSourceSpec f z fp ∧ ComplexHistoryCarrier fp ∧
          (exists h : BHist, exists q : BHist,
            CplxDiffQuot f z h q ∧ Cont f h q ∧ CplxNonZero h ∧ CplxNonZero q ∧
              hsame q fp) ∧
            (exists h : BHist, exists q : BHist,
              CplxDiffQuot f z h q ∧ Cont h q pattern ∧ CplxNonZero h ∧
                UnaryHistory h ∧ UnaryHistory q ∧ (hsame q BHist.Empty -> False)) ∧
              SemanticNameCert (CplxDiffAt f z) (CplxDiffAt f z) (CplxDiffAt f z)
                hsame := by
  intro diff patternSpec
  have sourceRows := CplxDiffAt_source_obligation_surface diff
  have quotientRows := CplxDiffAt_witness_nonzero_result diff
  have patternRows := CplxDiffPatternSpec_obligation_surface patternSpec
  have cert := complex_diff_semantic_name_certificate diff
  exact And.intro sourceRows.left
    (And.intro sourceRows.right.left
      (And.intro quotientRows
        (And.intro patternRows cert)))

end BEDC.Derived.ComplexDifferentiabilityUp
