import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.KoszulDualityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def KoszulDualityExtCarrier
    (derivedRow tensorRow extClassifier varianceLedger endpoint : BHist) : Prop :=
  UnaryHistory derivedRow ∧ UnaryHistory tensorRow ∧ UnaryHistory varianceLedger ∧
    Cont derivedRow tensorRow extClassifier ∧ Cont extClassifier varianceLedger endpoint

theorem KoszulDualityDerivedTensorLedger_exactness
    {derivedRow tensorRow extClassifier varianceLedger endpoint : BHist} :
    KoszulDualityExtCarrier derivedRow tensorRow extClassifier varianceLedger endpoint ->
      UnaryHistory extClassifier ∧ UnaryHistory endpoint ∧
        hsame extClassifier (append derivedRow tensorRow) ∧
          hsame endpoint (append extClassifier varianceLedger) := by
  intro carrier
  have derivedUnary : UnaryHistory derivedRow := carrier.left
  have tensorUnary : UnaryHistory tensorRow := carrier.right.left
  have varianceUnary : UnaryHistory varianceLedger := carrier.right.right.left
  have extRow : Cont derivedRow tensorRow extClassifier := carrier.right.right.right.left
  have endpointRow : Cont extClassifier varianceLedger endpoint := carrier.right.right.right.right
  have extUnary : UnaryHistory extClassifier :=
    unary_cont_closed derivedUnary tensorUnary extRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed extUnary varianceUnary endpointRow
  exact ⟨extUnary, endpointUnary, extRow, endpointRow⟩

theorem KoszulDualityExtCarrier_classifier_stability
    {derivedRow tensorRow extClassifier varianceLedger endpoint derivedRow' tensorRow'
      extClassifier' endpoint' : BHist} :
    KoszulDualityExtCarrier derivedRow tensorRow extClassifier varianceLedger endpoint ->
      hsame derivedRow derivedRow' -> hsame tensorRow tensorRow' ->
        Cont derivedRow' tensorRow' extClassifier' ->
          Cont extClassifier' varianceLedger endpoint' ->
            KoszulDualityExtCarrier derivedRow' tensorRow' extClassifier' varianceLedger
                endpoint' ∧
              hsame extClassifier extClassifier' ∧ hsame endpoint endpoint' := by
  intro carrier sameDerived sameTensor extRow' endpointRow'
  have derivedUnary' : UnaryHistory derivedRow' :=
    unary_transport carrier.left sameDerived
  have tensorUnary' : UnaryHistory tensorRow' :=
    unary_transport carrier.right.left sameTensor
  have extClassifierSame : hsame extClassifier extClassifier' :=
    cont_respects_hsame sameDerived sameTensor carrier.right.right.right.left extRow'
  have extClassifierUnary' : UnaryHistory extClassifier' :=
    unary_transport
      (unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.left)
      extClassifierSame
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame extClassifierSame (rfl : hsame varianceLedger varianceLedger)
      carrier.right.right.right.right endpointRow'
  exact
    ⟨⟨derivedUnary', tensorUnary', carrier.right.right.left, extRow', endpointRow'⟩,
      extClassifierSame, endpointSame⟩

end BEDC.Derived.KoszulDualityUp
