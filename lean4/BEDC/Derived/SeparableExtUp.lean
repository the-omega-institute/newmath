import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
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

def SeparableExtSourceRow [AskSetup] [PackageSetup]
    (field polynomial simple provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory field ∧ UnaryHistory polynomial ∧ UnaryHistory simple ∧
    UnaryHistory provenance ∧ UnaryHistory endpoint ∧
      Cont field polynomial provenance ∧ Cont provenance simple endpoint ∧
        PkgSig bundle endpoint pkg

theorem SeparableExtSourceRow_classifier_stability [AskSetup] [PackageSetup]
    {field field' polynomial polynomial' simple simple' provenance provenance'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableExtSourceRow field polynomial simple provenance endpoint bundle pkg ->
      hsame field field' ->
        hsame polynomial polynomial' ->
          hsame simple simple' ->
            Cont field' polynomial' provenance' ->
              Cont provenance' simple' endpoint' ->
                PkgSig bundle endpoint' pkg ->
                  SeparableExtSourceRow field' polynomial' simple' provenance' endpoint'
                      bundle pkg ∧
                    hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro row sameField samePolynomial sameSimple provenanceCont' endpointCont' pkgSig'
  have fieldUnary' : UnaryHistory field' :=
    unary_transport row.left sameField
  have polynomialUnary' : UnaryHistory polynomial' :=
    unary_transport row.right.left samePolynomial
  have simpleUnary' : UnaryHistory simple' :=
    unary_transport row.right.right.left sameSimple
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed fieldUnary' polynomialUnary' provenanceCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' simpleUnary' endpointCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameField samePolynomial row.right.right.right.right.right.left
      provenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameSimple row.right.right.right.right.right.right.left
      endpointCont'
  exact And.intro
    (And.intro fieldUnary'
      (And.intro polynomialUnary'
        (And.intro simpleUnary'
          (And.intro provenanceUnary'
            (And.intro endpointUnary'
              (And.intro provenanceCont'
                (And.intro endpointCont' pkgSig')))))))
    (And.intro sameProvenance sameEndpoint)

end BEDC.Derived.SeparableExtUp
