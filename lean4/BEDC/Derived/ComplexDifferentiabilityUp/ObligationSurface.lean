import BEDC.Derived.ComplexDifferentiabilityUp

namespace BEDC.Derived.ComplexDifferentiabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp

theorem CplxDiffPatternSpec_obligation_surface {f z pattern : BHist} :
    CplxDiffPatternSpec f z pattern ->
      exists h : BHist, exists q : BHist,
        CplxDiffQuot f z h q ∧ Cont h q pattern ∧ CplxNonZero h ∧
          UnaryHistory h ∧ UnaryHistory q ∧ (hsame q BHist.Empty -> False) := by
  intro patternSpec
  cases CplxDiffPatternSpec_witness_readback patternSpec with
  | intro h witness =>
      cases witness with
      | intro q data =>
          exact Exists.intro h
            (Exists.intro q
              (And.intro data.left
                (And.intro data.right.left
                  (And.intro data.left.right.right.left
                    (And.intro data.right.right.left
                      (And.intro data.right.right.right
                        (CplxDiffQuot_result_not_empty data.left)))))))

end BEDC.Derived.ComplexDifferentiabilityUp
