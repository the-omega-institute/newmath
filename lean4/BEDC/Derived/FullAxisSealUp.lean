import BEDC.Derived.AxisZeckendorf.AxisAdd
import BEDC.Derived.AxisZeckendorf.FullAxis

namespace BEDC.Derived.AxisZeckendorf.FullAxis

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem FullAxisSeal_source_exhaustion {h k : BHist} :
    FullAxisSourceSpec zeroSpinePrefixThread h ->
      FullAxisPatternSpec zeroSpinePrefixThread k ->
        FullAxisClassifierSpec zeroSpinePrefixThread h k ->
          FullAxisLedgerPolicy zeroSpinePrefixThread h ->
            ZeroSpine h ∧ ZeroSpine k ∧
              (hsame h (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
                (hsame k (BHist.e1 (BHist.e0 BHist.Empty)) -> False) := by
  intro sourceH patternK classifiedHK _ledgerH
  have hSpine : ZeroSpine h := sourceH
  have kSpine : ZeroSpine k := patternK
  have hBoundary :
      hsame h (BHist.e1 (BHist.e0 BHist.Empty)) -> False :=
    FullAxisSourceSpec_boundary_01_thread_separation sourceH
  have kBoundary :
      hsame k (BHist.e1 (BHist.e0 BHist.Empty)) -> False := by
    intro sameBoundary
    have boundarySpine : ZeroSpine (BHist.e1 (BHist.e0 BHist.Empty)) :=
      zeroSpine_hsame_transport classifiedHK.right sameBoundary
    exact zeroSpine_no_e1_extension boundarySpine
  exact And.intro hSpine (And.intro kSpine (And.intro hBoundary kBoundary))

theorem FullAxisPrefixThread_obligation_inventory {h k : BHist} :
    fullAxis_namecert.source h -> fullAxis_namecert.classifier h k ->
      fullAxis_namecert.ledger h ∧ FullAxisSourceSpec zeroSpinePrefixThread h ∧
        FullAxisPatternSpec zeroSpinePrefixThread k ∧
          FullAxisClassifierSpec zeroSpinePrefixThread h k ∧
            (hsame h (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
              (hsame k (BHist.e1 (BHist.e0 BHist.Empty)) -> False) := by
  intro sourceH classifiedHK
  have inventory :=
    FullAxisSeal_source_exhaustion sourceH classifiedHK.right classifiedHK sourceH
  exact And.intro sourceH
    (And.intro sourceH
      (And.intro classifiedHK.right
        (And.intro classifiedHK
          (And.intro inventory.right.right.left inventory.right.right.right))))

theorem FullAxisBoundaryMarker_finite_obligation :
    hsame boundary_01 (BHist.e1 (BHist.e0 BHist.Empty)) ∧
      (FullAxisSourceSpec zeroSpinePrefixThread boundary_01 -> False) ∧
        (FullAxisPatternSpec zeroSpinePrefixThread boundary_01 -> False) ∧
          (FullAxisLedgerPolicy zeroSpinePrefixThread boundary_01 -> False) := by
  constructor
  · rfl
  · constructor
    · exact boundary_01_not_zeroSpine
    · constructor
      · exact boundary_01_not_zeroSpine
      · exact boundary_01_not_zeroSpine

theorem FullAxisSeal_real_route_separation_obligation {h k r : BHist} :
    FullAxisSourceSpec zeroSpinePrefixThread h ->
      FullAxisPatternSpec zeroSpinePrefixThread k ->
        Cont h k r ->
          ZeroSpine r ∧ (hsame r (BHist.e1 (BHist.e0 BHist.Empty)) -> False) := by
  intro sourceH patternK contHK
  have resultSpine : ZeroSpine r :=
    BEDC.Derived.AxisZeckendorf.AxisAdd.AxisAddCont_result_zeroSpine sourceH patternK contHK
  have boundaryExcluded : hsame r (BHist.e1 (BHist.e0 BHist.Empty)) -> False := by
    intro sameBoundary
    have boundarySpine : ZeroSpine (BHist.e1 (BHist.e0 BHist.Empty)) :=
      zeroSpine_hsame_transport resultSpine sameBoundary
    exact zeroSpine_no_e1_extension boundarySpine
  exact And.intro resultSpine boundaryExcluded

end BEDC.Derived.AxisZeckendorf.FullAxis
