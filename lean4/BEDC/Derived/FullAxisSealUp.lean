import BEDC.Derived.AxisZeckendorf.FullAxis

namespace BEDC.Derived.AxisZeckendorf.FullAxis

open BEDC.FKernel.Hist
open BEDC.Derived.AxisZeckendorf.Spine

theorem FullAxisSourceSpec_boundary_01_thread_separation {h : BHist} :
    FullAxisSourceSpec zeroSpinePrefixThread h ->
      hsame h (BHist.e1 (BHist.e0 BHist.Empty)) -> False := by
  intro sourceH sameBoundary
  have boundarySpine : ZeroSpine (BHist.e1 (BHist.e0 BHist.Empty)) :=
    zeroSpine_hsame_transport sourceH sameBoundary
  exact zeroSpine_no_e1_extension boundarySpine

theorem FullAxis_e1_e0_empty_boundary_exclusion :
    (FullAxisSourceSpec zeroSpinePrefixThread (BHist.e1 (BHist.e0 BHist.Empty)) ->
        False) ∧
      (FullAxisPatternSpec zeroSpinePrefixThread (BHist.e1 (BHist.e0 BHist.Empty)) ->
        False) ∧
        (FullAxisLedgerPolicy zeroSpinePrefixThread (BHist.e1 (BHist.e0 BHist.Empty)) ->
          False) ∧
          (forall {h : BHist},
            FullAxisClassifierSpec zeroSpinePrefixThread (BHist.e1 (BHist.e0 BHist.Empty))
              h ->
                False) := by
  constructor
  · intro sourceBoundary
    exact zeroSpine_no_e1_extension sourceBoundary
  · constructor
    · intro patternBoundary
      exact zeroSpine_no_e1_extension patternBoundary
    · constructor
      · intro ledgerBoundary
        exact zeroSpine_no_e1_extension ledgerBoundary
      · intro h classifiedBoundary
        exact zeroSpine_no_e1_extension classifiedBoundary.left

end BEDC.Derived.AxisZeckendorf.FullAxis
