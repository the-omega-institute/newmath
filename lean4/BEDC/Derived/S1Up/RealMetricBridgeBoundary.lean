import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

theorem SOneRealMetricBridgeBoundary_public_rows {x y equation point metricLedger : BHist} :
    SOneHistoryCarrier x y equation point -> Cont point equation metricLedger ->
      UnaryHistory metricLedger ∧ hsame metricLedger (append point equation) ∧
        SOneProductHistoryCarrier point ∧ hsame equation SOneUnitHistory := by
  intro carrier metricCont
  have readback := SOneHistoryCarrier_public_readback carrier
  have realConstantUnary :
      ∀ {row : BHist}, RealConstantHistoryCarrier row -> UnaryHistory row := by
    intro row rowCarrier
    cases rowCarrier with
    | intro denominator data =>
        have denominatorUnary : UnaryHistory denominator :=
          (PositiveUnaryDenominator_unary_and_nonempty
            (RatHistoryCarrier_iff_positive_denominator.mp data.right)).left
        exact unary_transport (unary_e1_closed denominatorUnary) (hsame_symm data.left)
  have pointUnary : UnaryHistory point :=
    ProdHistoryCarrier_unary_of_components realConstantUnary realConstantUnary readback.left
  have equationUnary : UnaryHistory equation :=
    unary_transport (unary_double_e1_closed unary_empty) (hsame_symm readback.right.left)
  have metricUnary : UnaryHistory metricLedger :=
    unary_cont_closed pointUnary equationUnary metricCont
  exact ⟨metricUnary, metricCont, readback.left, readback.right.left⟩

theorem SOneRegSeqRatMetricObservationBoundary_public_rows
    {x y equation point metricLedger : BHist} :
    SOneHistoryCarrier x y equation point -> Cont point equation metricLedger ->
      UnaryHistory metricLedger ∧ SOneProductHistoryCarrier point ∧
        hsame equation SOneUnitHistory ∧
          exists dx dy : BHist,
            hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
              hsame y (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x y point := by
  intro carrier metricCont
  have metricRows := SOneRealMetricBridgeBoundary_public_rows carrier metricCont
  have readback := SOneHistoryCarrier_public_readback carrier
  exact And.intro metricRows.left
    (And.intro metricRows.right.right.left
      (And.intro metricRows.right.right.right readback.right.right))

theorem SOneStandardTopologicalBridgeBoundary_component_rows
    {x y equation point bridge : BHist} :
    SOneHistoryCarrier x y equation point -> Cont point equation bridge ->
      ∃ dx dy : BHist,
        hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧ hsame y (BHist.e1 dy) ∧
          RatHistoryCarrier dy ∧ SOneProductHistoryCarrier point ∧
            hsame equation SOneUnitHistory ∧ UnaryHistory bridge ∧
              hsame bridge (append point equation) := by
  intro carrier bridgeRow
  have readback := SOneHistoryCarrier_public_readback carrier
  have bridgeBoundary := SOneRealMetricBridgeBoundary_public_rows carrier bridgeRow
  cases readback.right.right with
  | intro dx dxRows =>
      cases dxRows with
      | intro dy dyRows =>
          exact Exists.intro dx
            (Exists.intro dy
              (And.intro dyRows.left
                (And.intro dyRows.right.left
                  (And.intro dyRows.right.right.left
                    (And.intro dyRows.right.right.right.left
                      (And.intro bridgeBoundary.right.right.left
                        (And.intro bridgeBoundary.right.right.right
                          (And.intro bridgeBoundary.left bridgeBoundary.right.left))))))))

end BEDC.Derived.S1Up
