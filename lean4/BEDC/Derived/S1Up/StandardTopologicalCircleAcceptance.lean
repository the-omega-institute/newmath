import BEDC.Derived.S1Up.StandardTopologicalBridgeBoundary

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem SOneStandardTopologicalCircleAcceptance_factorization_public_rows
    {x y equation point metricLedger bridgeLedger : BHist} :
    SOneHistoryCarrier x y equation point ->
      Cont point equation metricLedger ->
        Cont metricLedger equation bridgeLedger ->
          exists dx dy : BHist,
            hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
              hsame y (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧
                SOneProductHistoryCarrier point ∧ hsame equation SOneUnitHistory ∧
                  UnaryHistory bridgeLedger ∧
                    hsame bridgeLedger (append (append point equation) equation) ∧
                      (hsame bridgeLedger BHist.Empty -> False) := by
  intro carrier metricRow bridgeRow
  have bridgeRows :=
    SOneStandardTopologicalBridgeBoundary_public_rows carrier metricRow bridgeRow
  have readback := SOneHistoryCarrier_public_readback carrier
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
                      (And.intro bridgeRows.right.right.left
                        (And.intro bridgeRows.right.right.right.left
                          (And.intro bridgeRows.left
                            (And.intro bridgeRows.right.left
                              bridgeRows.right.right.right.right)))))))))

end BEDC.Derived.S1Up
