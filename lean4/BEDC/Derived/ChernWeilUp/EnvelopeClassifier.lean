import BEDC.Derived.ChernWeilUp

namespace BEDC.Derived.ChernWeilUp

open BEDC.FKernel.Hist

def ChernWeilEnvelopeCharacteristicClassifier
    (curvature curvature' derham derham' provenance provenance' connectionLedger
      connectionLedger' classRow classRow' : BHist) : Prop :=
  ChernWeilSourceEnvelope curvature derham provenance connectionLedger classRow ∧
    ChernWeilSourceEnvelope curvature' derham' provenance' connectionLedger' classRow' ∧
      hsame curvature curvature' ∧ hsame derham derham' ∧ hsame classRow classRow'

theorem ChernWeilEnvelopeCharacteristicClassifier_transport
    {curvature curvature' derham derham' provenance provenance' connectionLedger
      connectionLedger' classRow classRow' : BHist} :
    ChernWeilEnvelopeCharacteristicClassifier curvature curvature' derham derham'
        provenance provenance' connectionLedger connectionLedger' classRow classRow' ->
      ChernWeilSourceEnvelope curvature' derham' provenance' connectionLedger' classRow' ∧
        hsame classRow classRow' := by
  intro classifier
  exact And.intro classifier.right.left classifier.right.right.right.right

end BEDC.Derived.ChernWeilUp
