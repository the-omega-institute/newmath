import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

theorem SOneStandardTopologicalBridgeBoundary_public_rows
    {x y equation point metricLedger bridgeLedger : BHist} :
    SOneHistoryCarrier x y equation point ->
      Cont point equation metricLedger ->
        Cont metricLedger equation bridgeLedger ->
          UnaryHistory bridgeLedger ∧ hsame bridgeLedger (append (append point equation) equation) ∧
            SOneProductHistoryCarrier point ∧ hsame equation SOneUnitHistory ∧
              (hsame bridgeLedger BHist.Empty -> False) := by
  intro carrier metricRow bridgeRow
  have readback := SOneHistoryCarrier_public_readback carrier
  have equationUnary : UnaryHistory equation := by
    have equationSame : hsame equation (BHist.e1 (BHist.e1 BHist.Empty)) :=
      readback.right.left
    exact unary_transport (unary_e1_closed (unary_e1_closed unary_empty))
      (hsame_symm equationSame)
  have pointUnary : UnaryHistory point := by
    cases carrier with
    | intro xCarrier rest =>
        cases rest with
        | intro yCarrier rest =>
            cases rest with
            | intro _equationCarrier pointCont =>
                cases xCarrier with
                | intro dx xData =>
                    cases yCarrier with
                    | intro dy yData =>
                        exact unary_cont_closed
                          (unary_transport (unary_e1_closed
                            (PositiveUnaryDenominator_unary_and_nonempty
                              (RatHistoryCarrier_iff_positive_denominator.mp xData.right)).left)
                            (hsame_symm xData.left))
                          (unary_transport (unary_e1_closed
                            (PositiveUnaryDenominator_unary_and_nonempty
                              (RatHistoryCarrier_iff_positive_denominator.mp yData.right)).left)
                            (hsame_symm yData.left))
                          pointCont
  have metricUnary : UnaryHistory metricLedger :=
    unary_cont_closed pointUnary equationUnary metricRow
  have bridgeUnary : UnaryHistory bridgeLedger :=
    unary_cont_closed metricUnary equationUnary bridgeRow
  have bridgeShape : hsame bridgeLedger (append (append point equation) equation) := by
    cases metricRow
    exact bridgeRow
  have bridgeNonempty : hsame bridgeLedger BHist.Empty -> False := by
    intro sameEmpty
    have equationEmpty : equation = BHist.Empty :=
      (append_eq_empty_iff.mp (bridgeRow.symm.trans sameEmpty)).right
    exact not_hsame_e1_empty
      (hsame_trans (hsame_symm readback.right.left) equationEmpty)
  exact ⟨bridgeUnary, bridgeShape, readback.left, readback.right.left, bridgeNonempty⟩

end BEDC.Derived.S1Up
