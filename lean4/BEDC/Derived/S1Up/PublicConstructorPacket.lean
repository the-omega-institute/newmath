import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def SOnePublicConstructorPacket
    (x y e p x' y' e' p' provenance publicLedger : BHist) : Prop :=
  SOneComponentClassifier x y e p x' y' e' p' ∧ Cont provenance p' publicLedger ∧
    SemanticNameCert (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
      (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
      (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
      hsame

theorem SOnePublicConstructorPacket_scope
    {x y e p x' y' e' p' provenance publicLedger : BHist} :
    SOnePublicConstructorPacket x y e p x' y' e' p' provenance publicLedger ->
      SOneComponentClassifier x y e p x' y' e' p' ∧ SOneProductHistoryCarrier p ∧
        SOneProductHistoryCarrier p' ∧ hsame e SOneUnitHistory ∧
          hsame e' SOneUnitHistory ∧ hsame p p' ∧ Cont x y p ∧
            Cont x' y' p' ∧ hsame publicLedger (append provenance p') := by
  intro packet
  have classifier : SOneComponentClassifier x y e p x' y' e' p' :=
    packet.left
  have sourceReadback := SOneHistoryCarrier_public_readback classifier.left
  have targetReadback := SOneComponentClassifier_public_readback classifier
  have ledgerDeterminacy :=
    SOneHistoryCarrier_component_classifier_ledger_determinacy classifier.left
      classifier.right.left classifier.right.right.left classifier.right.right.right
  have publicLedgerRow : Cont provenance p' publicLedger :=
    packet.right.left
  exact And.intro classifier
    (And.intro sourceReadback.left
      (And.intro targetReadback.left
        (And.intro sourceReadback.right.left
          (And.intro targetReadback.right.left
            (And.intro ledgerDeterminacy.right
              (And.intro classifier.left.right.right.right
                (And.intro classifier.right.left.right.right.right
                  publicLedgerRow)))))))

end BEDC.Derived.S1Up
