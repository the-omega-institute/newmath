import BEDC.FKernel.Cont
import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldExtUp
open BEDC.Derived.PolynomialUp

def SeparableExtSingletonCarrier
    (extension minimalRoot simpleRoot ledger : BHist) : Prop :=
  FieldExtSingletonCarrier extension ∧ PolynomialSingletonCarrier minimalRoot ∧
    PolynomialSingletonCarrier simpleRoot ∧ Cont minimalRoot simpleRoot ledger

theorem SeparableExtSingleton_carrier_classifier_surface
    {extension minimalRoot simpleRoot ledger extension' minimalRoot' simpleRoot' ledger' : BHist} :
    SeparableExtSingletonCarrier extension minimalRoot simpleRoot ledger ->
      FieldExtSingletonClassifier extension extension' ->
      PolynomialSingletonClassifier minimalRoot minimalRoot' ->
      PolynomialSingletonClassifier simpleRoot simpleRoot' ->
      Cont minimalRoot' simpleRoot' ledger' ->
        SeparableExtSingletonCarrier extension' minimalRoot' simpleRoot' ledger' ∧
          hsame ledger ledger' := by
  intro carrier extensionClassified minimalClassified simpleClassified ledgerRow'
  have extensionCarrier' : FieldExtSingletonCarrier extension' :=
    And.intro extensionClassified.left.right.left extensionClassified.right.right.left
  have ledgerSame : hsame ledger ledger' :=
    cont_respects_hsame minimalClassified.right.right simpleClassified.right.right
      carrier.right.right.right ledgerRow'
  exact And.intro
    (And.intro extensionCarrier'
      (And.intro minimalClassified.right.left
        (And.intro simpleClassified.right.left ledgerRow')))
    ledgerSame

end BEDC.Derived.SeparableExtUp
