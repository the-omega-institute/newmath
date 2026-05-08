import BEDC.FKernel.Cont
import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldExtUp
open BEDC.Derived.PolynomialUp

def GaloisExtSourcePacket
    (field minimalRoot simpleRoot sepLedger normality ledger : BHist) : Prop :=
  FieldExtSingletonCarrier field ∧ PolynomialSingletonCarrier normality ∧
    PolynomialSingletonCarrier minimalRoot ∧ PolynomialSingletonCarrier simpleRoot ∧
      Cont minimalRoot simpleRoot sepLedger ∧ Cont field normality ledger

theorem GaloisExtSourcePacket_classifier_transport_row
    {field minimalRoot simpleRoot sepLedger normality ledger field' minimalRoot'
      simpleRoot' sepLedger' normality' ledger' : BHist} :
    GaloisExtSourcePacket field minimalRoot simpleRoot sepLedger normality ledger ->
      FieldExtSingletonClassifier field field' ->
      PolynomialSingletonClassifier minimalRoot minimalRoot' ->
      PolynomialSingletonClassifier simpleRoot simpleRoot' ->
      hsame normality normality' ->
      Cont minimalRoot' simpleRoot' sepLedger' ->
      Cont field' normality' ledger' ->
        GaloisExtSourcePacket field' minimalRoot' simpleRoot' sepLedger' normality' ledger' ∧
          hsame ledger ledger' := by
  intro packet fieldClassified minimalClassified simpleClassified sameNormality sepRow' ledgerRow'
  have fieldCarrier' : FieldExtSingletonCarrier field' :=
    And.intro fieldClassified.left.right.left fieldClassified.right.right.left
  have normalityCarrier' : PolynomialSingletonCarrier normality' :=
    hsame_trans (hsame_symm sameNormality) packet.right.left
  have ledgerSame : hsame ledger ledger' :=
    cont_respects_hsame fieldClassified.left.right.right sameNormality
      packet.right.right.right.right.right ledgerRow'
  exact And.intro
    (And.intro fieldCarrier'
      (And.intro normalityCarrier'
        (And.intro minimalClassified.right.left
          (And.intro simpleClassified.right.left
            (And.intro sepRow' ledgerRow')))))
    ledgerSame

end BEDC.Derived.GaloisExtUp
