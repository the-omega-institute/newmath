import BEDC.FKernel.Cont
import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
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

theorem GaloisExtSourcePacket_classifier_transport
    {field field' separable separable' normal normal' simple simple' classifier classifier'
      provenance provenance' ledger ledger' : BHist} :
    UnaryHistory field ->
      UnaryHistory separable ->
        UnaryHistory normal ->
          UnaryHistory simple ->
            hsame field field' ->
              hsame separable separable' ->
                hsame normal normal' ->
                  hsame simple simple' ->
                    Cont field separable classifier ->
                      Cont normal simple provenance ->
                        Cont classifier provenance ledger ->
                          Cont field' separable' classifier' ->
                            Cont normal' simple' provenance' ->
                              Cont classifier' provenance' ledger' ->
                                UnaryHistory classifier' ∧ UnaryHistory provenance' ∧
                                  UnaryHistory ledger' ∧ hsame classifier classifier' ∧
                                    hsame provenance provenance' ∧ hsame ledger ledger' := by
  intro fieldUnary separableUnary normalUnary simpleUnary sameField sameSeparable sameNormal
    sameSimple classifierCont provenanceCont ledgerCont classifierCont' provenanceCont'
    ledgerCont'
  have fieldUnary' : UnaryHistory field' :=
    unary_transport fieldUnary sameField
  have separableUnary' : UnaryHistory separable' :=
    unary_transport separableUnary sameSeparable
  have normalUnary' : UnaryHistory normal' :=
    unary_transport normalUnary sameNormal
  have simpleUnary' : UnaryHistory simple' :=
    unary_transport simpleUnary sameSimple
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed fieldUnary' separableUnary' classifierCont'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed normalUnary' simpleUnary' provenanceCont'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed classifierUnary' provenanceUnary' ledgerCont'
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameField sameSeparable classifierCont classifierCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameNormal sameSimple provenanceCont provenanceCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameClassifier sameProvenance ledgerCont ledgerCont'
  exact And.intro classifierUnary'
    (And.intro provenanceUnary'
      (And.intro ledgerUnary'
        (And.intro sameClassifier
          (And.intro sameProvenance sameLedger))))

end BEDC.Derived.GaloisExtUp
