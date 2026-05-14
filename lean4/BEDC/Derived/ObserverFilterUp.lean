import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem ObserverFilter_ledger_exactness [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ObserverFilterCarrier source selected omitted transport ledger routes provenance
            localName bundle pkg ∧
            hsame row omitted)
        (fun _row : BHist => Cont source selected ledger ∧ Cont ledger omitted routes ∧
          PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig SemanticNameCert
  intro carrier
  obtain ⟨sourceUnary, selectedUnary, omittedUnary, ledgerUnary, routesUnary,
    provenanceUnary, localNameUnary, sourceSelected, ledgerOmitted, routesLocalName,
    pkgSig⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro omitted (And.intro
          ⟨sourceUnary, selectedUnary, omittedUnary, ledgerUnary, routesUnary,
            provenanceUnary, localNameUnary, sourceSelected, ledgerOmitted, routesLocalName,
            pkgSig⟩
          (hsame_refl omitted))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceData
        exact And.intro sourceData.left (hsame_trans (hsame_symm sameRows) sourceData.right)
    }
    pattern_sound := by
      intro row sourceData
      exact And.intro sourceSelected (And.intro ledgerOmitted pkgSig)
    ledger_sound := by
      intro row sourceData
      exact And.intro (unary_transport omittedUnary (hsame_symm sourceData.right)) pkgSig
  }

theorem ObserverFilterCarrier_streamname_handoff [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg →
      Cont selected ledger streamRead →
        UnaryHistory selected ∧ UnaryHistory ledger ∧ UnaryHistory streamRead ∧
          Cont source selected ledger ∧ Cont selected ledger streamRead ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectedLedger
  obtain ⟨_sourceUnary, selectedUnary, _omittedUnary, ledgerUnary, _routesUnary,
    _provenanceUnary, _localNameUnary, sourceSelected, _ledgerOmitted,
    _routesLocalName, pkgSig⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed selectedUnary ledgerUnary selectedLedger
  exact ⟨selectedUnary, ledgerUnary, streamUnary, sourceSelected, selectedLedger, pkgSig⟩

theorem ObserverFilter_streamname_handoff [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg →
      Cont selected localName streamRead →
        UnaryHistory selected ∧ UnaryHistory ledger ∧ UnaryHistory routes ∧
          UnaryHistory provenance ∧ UnaryHistory localName ∧ UnaryHistory streamRead ∧
            Cont source selected ledger ∧ Cont routes localName provenance ∧
              Cont selected localName streamRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectedLocalName
  obtain ⟨_sourceUnary, selectedUnary, _omittedUnary, ledgerUnary, routesUnary,
    provenanceUnary, localNameUnary, sourceSelected, _ledgerOmitted, routesLocalName,
    pkgSig⟩ := carrier
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed selectedUnary localNameUnary selectedLocalName
  exact
    ⟨selectedUnary, ledgerUnary, routesUnary, provenanceUnary, localNameUnary,
      streamReadUnary, sourceSelected, routesLocalName, selectedLocalName, pkgSig⟩

end BEDC.Derived.ObserverFilterUp
