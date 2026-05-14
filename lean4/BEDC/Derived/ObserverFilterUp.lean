import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObserverFilterCarrier [AskSetup] [PackageSetup]
    (source selected omitted transport ledger routes provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory source ∧ UnaryHistory selected ∧ UnaryHistory omitted ∧
    UnaryHistory ledger ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
      UnaryHistory localName ∧ Cont source selected ledger ∧
        Cont ledger omitted routes ∧ Cont routes localName provenance ∧
          PkgSig bundle provenance pkg

theorem ObserverFilterCarrier_identity_stability [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName source' selected'
      omitted' transport' ledger' routes' provenance' localName' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg →
      hsame source source' →
        hsame selected selected' →
          hsame omitted omitted' →
            hsame localName localName' →
              Cont source' selected' ledger' →
                Cont ledger' omitted' routes' →
                  Cont routes' localName' provenance' →
                    PkgSig bundle provenance' pkg →
                      ObserverFilterCarrier source' selected' omitted' transport' ledger'
                          routes' provenance' localName' bundle pkg ∧
                        hsame ledger ledger' ∧ hsame routes routes' ∧
                          hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier sameSource sameSelected sameOmitted sameLocalName sourceSelected'
    ledgerOmitted' routesLocalName' pkgSig'
  obtain ⟨sourceUnary, selectedUnary, omittedUnary, _ledgerUnary, _routesUnary,
    _provenanceUnary, localNameUnary, sourceSelected, ledgerOmitted, routesLocalName,
    _pkgSig⟩ := carrier
  have sourceUnary' : UnaryHistory source' :=
    unary_transport sourceUnary sameSource
  have selectedUnary' : UnaryHistory selected' :=
    unary_transport selectedUnary sameSelected
  have omittedUnary' : UnaryHistory omitted' :=
    unary_transport omittedUnary sameOmitted
  have localNameUnary' : UnaryHistory localName' :=
    unary_transport localNameUnary sameLocalName
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed sourceUnary' selectedUnary' sourceSelected'
  have routesUnary' : UnaryHistory routes' :=
    unary_cont_closed ledgerUnary' omittedUnary' ledgerOmitted'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed routesUnary' localNameUnary' routesLocalName'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameSource sameSelected sourceSelected sourceSelected'
  have sameRoutes : hsame routes routes' :=
    cont_respects_hsame sameLedger sameOmitted ledgerOmitted ledgerOmitted'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRoutes sameLocalName routesLocalName routesLocalName'
  exact
    ⟨⟨sourceUnary', selectedUnary', omittedUnary', ledgerUnary', routesUnary',
        provenanceUnary', localNameUnary', sourceSelected', ledgerOmitted',
        routesLocalName', pkgSig'⟩,
      sameLedger, sameRoutes, sameProvenance⟩

end BEDC.Derived.ObserverFilterUp
