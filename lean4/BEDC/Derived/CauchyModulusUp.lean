import BEDC.Derived.RatUp

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def CauchyModulusLedgerPacket
    (precision threshold tolerance observation consumption provenance window : BHist) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ RatHistoryCarrier tolerance ∧
    Cont precision threshold window ∧ Cont window tolerance consumption ∧
      Cont consumption observation provenance

theorem CauchyModulusLedgerPacket_hsame_stability
    {precision precision' threshold threshold' tolerance tolerance' observation observation'
      consumption provenance window : BHist} :
    CauchyModulusLedgerPacket precision threshold tolerance observation consumption provenance window ->
      hsame precision' precision -> hsame threshold' threshold -> hsame tolerance' tolerance ->
        hsame observation' observation ->
          exists consumption' provenance' window' : BHist,
            CauchyModulusLedgerPacket precision' threshold' tolerance' observation'
              consumption' provenance' window' ∧
              hsame window window' ∧ hsame consumption consumption' ∧
                hsame provenance provenance' := by
  intro packet samePrecision sameThreshold sameTolerance sameObservation
  cases packet with
  | intro precisionUnary packetRest =>
      cases packetRest with
      | intro thresholdUnary packetRest =>
          cases packetRest with
          | intro toleranceCarrier packetRest =>
              cases packetRest with
              | intro windowRow packetRest =>
                  cases packetRest with
                  | intro consumptionRow provenanceRow =>
                      let window' := append precision' threshold'
                      let consumption' := append window' tolerance'
                      let provenance' := append consumption' observation'
                      have precisionUnary' : UnaryHistory precision' :=
                        unary_transport_symm precisionUnary samePrecision
                      have thresholdUnary' : UnaryHistory threshold' :=
                        unary_transport_symm thresholdUnary sameThreshold
                      have toleranceCarrier' : RatHistoryCarrier tolerance' :=
                        RatHistoryCarrier_hsame_transport (hsame_symm sameTolerance)
                          toleranceCarrier
                      have windowRow' : Cont precision' threshold' window' := by
                        rfl
                      have consumptionRow' : Cont window' tolerance' consumption' := by
                        rfl
                      have provenanceRow' : Cont consumption' observation' provenance' := by
                        rfl
                      have sameWindow : hsame window window' :=
                        cont_respects_hsame (hsame_symm samePrecision)
                          (hsame_symm sameThreshold) windowRow windowRow'
                      have sameConsumption : hsame consumption consumption' :=
                        cont_respects_hsame sameWindow (hsame_symm sameTolerance)
                          consumptionRow consumptionRow'
                      have sameProvenance : hsame provenance provenance' :=
                        cont_respects_hsame sameConsumption (hsame_symm sameObservation)
                          provenanceRow provenanceRow'
                      exact ⟨consumption', provenance', window',
                        ⟨precisionUnary', thresholdUnary', toleranceCarrier', windowRow',
                          consumptionRow', provenanceRow'⟩,
                        sameWindow, sameConsumption, sameProvenance⟩

end BEDC.Derived.CauchyModulusUp
