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

theorem ObserverFilterCarrier_observer_history_factorization [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          ObserverFilterCarrier source selected omitted transport ledger routes provenance
              localName bundle pkg ∧
            (hsame row source ∨ hsame row selected ∨ hsame row omitted))
        (fun _row : BHist =>
          Cont source selected ledger ∧ Cont ledger omitted routes ∧
            Cont routes localName provenance ∧ PkgSig bundle provenance pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨sourceUnary, selectedUnary, omittedUnary, _ledgerUnary, _routesUnary,
    _provenanceUnary, _localNameUnary, sourceSelected, ledgerOmitted, routesLocalName,
    pkgSig⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro source
          (And.intro carrierWitness (Or.inl (hsame_refl source)))
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
        constructor
        · exact sourceData.left
        · cases sourceData.right with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
          | inr rest =>
              cases rest with
              | inl sameSelected =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSelected))
              | inr sameOmitted =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameOmitted))
    }
    pattern_sound := by
      intro _row _sourceData
      exact ⟨sourceSelected, ledgerOmitted, routesLocalName, pkgSig⟩
    ledger_sound := by
      intro row sourceData
      cases sourceData.right with
      | inl sameSource =>
          exact And.intro (unary_transport sourceUnary (hsame_symm sameSource)) pkgSig
      | inr rest =>
          cases rest with
          | inl sameSelected =>
              exact And.intro (unary_transport selectedUnary (hsame_symm sameSelected)) pkgSig
          | inr sameOmitted =>
              exact And.intro (unary_transport omittedUnary (hsame_symm sameOmitted)) pkgSig
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

theorem ObserverFilterCarrier_selected_row_totality [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName selectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg →
      Cont selected ledger selectedRead →
        PkgSig bundle selectedRead pkg →
          UnaryHistory source ∧ UnaryHistory selected ∧ UnaryHistory ledger ∧
            UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
              UnaryHistory selectedRead ∧ Cont source selected ledger ∧
                Cont selected ledger selectedRead ∧ Cont routes localName provenance ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle selectedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectedLedger selectedPkg
  obtain ⟨sourceUnary, selectedUnary, _omittedUnary, ledgerUnary, routesUnary,
    provenanceUnary, localNameUnary, sourceSelected, _ledgerOmitted, routesLocalName,
    provenancePkg⟩ := carrier
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed selectedUnary ledgerUnary selectedLedger
  exact
    ⟨sourceUnary, selectedUnary, ledgerUnary, routesUnary, provenanceUnary,
      localNameUnary, selectedReadUnary, sourceSelected, selectedLedger,
      routesLocalName, provenancePkg, selectedPkg⟩

theorem ObserverFilterCarrier_omitted_row_boundary_exhaustion [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName omittedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg →
      Cont ledger omitted omittedRead →
        PkgSig bundle omittedRead pkg →
          UnaryHistory source ∧ UnaryHistory omitted ∧ UnaryHistory ledger ∧
            UnaryHistory routes ∧ UnaryHistory omittedRead ∧ Cont source selected ledger ∧
              Cont ledger omitted routes ∧ Cont ledger omitted omittedRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle omittedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier ledgerOmittedRead omittedReadPkg
  obtain ⟨sourceUnary, _selectedUnary, omittedUnary, ledgerUnary, routesUnary,
    _provenanceUnary, _localNameUnary, sourceSelected, ledgerOmitted, _routesLocalName,
    provenancePkg⟩ := carrier
  have omittedReadUnary : UnaryHistory omittedRead :=
    unary_cont_closed ledgerUnary omittedUnary ledgerOmittedRead
  exact
    ⟨sourceUnary, omittedUnary, ledgerUnary, routesUnary, omittedReadUnary, sourceSelected,
      ledgerOmitted, ledgerOmittedRead, provenancePkg, omittedReadPkg⟩

theorem ObserverFilterCarrier_streamname_selected_subhistory_nonescape [AskSetup]
    [PackageSetup]
    {source selected omitted transport ledger routes provenance localName streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg →
      Cont selected localName streamRead →
        PkgSig bundle streamRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ObserverFilterCarrier source selected omitted transport ledger routes provenance
                    localName bundle pkg ∧
                  hsame row selected)
              (fun row : BHist =>
                Cont selected localName streamRead ∧ hsame row selected ∧
                  PkgSig bundle streamRead pkg)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle streamRead pkg)
              hsame ∧
            UnaryHistory selected ∧ UnaryHistory streamRead ∧
              Cont source selected ledger ∧ Cont selected localName streamRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle streamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert
  intro carrier selectedLocalName streamPkg
  have carrierWitness :
      ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg := carrier
  obtain ⟨_sourceUnary, selectedUnary, _omittedUnary, _ledgerUnary, _routesUnary,
    _provenanceUnary, localNameUnary, sourceSelected, _ledgerOmitted, _routesLocalName,
    provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed selectedUnary localNameUnary selectedLocalName
  have sourceAtSelected :
      ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
          bundle pkg ∧
        hsame selected selected :=
    And.intro carrierWitness (hsame_refl selected)
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ObserverFilterCarrier source selected omitted transport ledger routes provenance
              localName bundle pkg ∧
            hsame row selected)
        (fun row : BHist =>
          Cont selected localName streamRead ∧ hsame row selected ∧
            PkgSig bundle streamRead pkg)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle streamRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro selected sourceAtSelected
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
        exact And.intro sourceData.left
          (hsame_trans (hsame_symm sameRows) sourceData.right)
    }
    pattern_sound := by
      intro row sourceData
      exact ⟨selectedLocalName, sourceData.right, streamPkg⟩
    ledger_sound := by
      intro row sourceData
      exact
        ⟨unary_transport selectedUnary (hsame_symm sourceData.right), provenancePkg,
          streamPkg⟩
  }
  exact
    ⟨cert, selectedUnary, streamUnary, sourceSelected, selectedLocalName, provenancePkg,
      streamPkg⟩

theorem ObserverFilterCarrier_budget_selector_l10_handoff [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName budgetSchedule
      budgetWindows budgetRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg →
      UnaryHistory budgetSchedule →
      Cont selected budgetSchedule budgetWindows →
        Cont budgetWindows localName budgetRoute →
          PkgSig bundle budgetRoute pkg →
            UnaryHistory selected ∧ UnaryHistory budgetSchedule ∧
              UnaryHistory budgetWindows ∧ UnaryHistory budgetRoute ∧
                Cont source selected ledger ∧
                  Cont selected budgetSchedule budgetWindows ∧
                    Cont budgetWindows localName budgetRoute ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle budgetRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier budgetScheduleUnary selectedBudget budgetLocalName budgetPkg
  obtain ⟨_sourceUnary, selectedUnary, _omittedUnary, _ledgerUnary, _routesUnary,
    _provenanceUnary, localNameUnary, sourceSelected, _ledgerOmitted, _routesLocalName,
    provenancePkg⟩ := carrier
  have budgetWindowsUnary : UnaryHistory budgetWindows :=
    unary_cont_closed selectedUnary budgetScheduleUnary selectedBudget
  have budgetRouteUnary : UnaryHistory budgetRoute :=
    unary_cont_closed budgetWindowsUnary localNameUnary budgetLocalName
  exact
    ⟨selectedUnary, budgetScheduleUnary, budgetWindowsUnary, budgetRouteUnary,
      sourceSelected, selectedBudget, budgetLocalName, provenancePkg, budgetPkg⟩

theorem ObserverFilterCarrier_real_window_budget_exhaustion [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName budgetSchedule
      budgetWindows budgetRoute realWindow realRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg →
      UnaryHistory budgetSchedule →
        UnaryHistory realWindow →
      Cont selected budgetSchedule budgetWindows →
        Cont budgetWindows realWindow budgetRoute →
          Cont budgetRoute localName realRoute →
            PkgSig bundle realRoute pkg →
              UnaryHistory source ∧ UnaryHistory selected ∧ UnaryHistory omitted ∧
                UnaryHistory budgetWindows ∧ UnaryHistory realRoute ∧
                  Cont source selected ledger ∧ Cont ledger omitted routes ∧
                    Cont selected budgetSchedule budgetWindows ∧
                      Cont budgetWindows realWindow budgetRoute ∧
                        Cont budgetRoute localName realRoute ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle realRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier budgetScheduleUnary realWindowUnary selectedBudget budgetRealWindow budgetLocalName
    realRoutePkg
  obtain ⟨sourceUnary, selectedUnary, omittedUnary, _ledgerUnary, _routesUnary,
    _provenanceUnary, localNameUnary, sourceSelected, ledgerOmitted, _routesLocalName,
    provenancePkg⟩ := carrier
  have budgetWindowsUnary : UnaryHistory budgetWindows :=
    unary_cont_closed selectedUnary budgetScheduleUnary selectedBudget
  have budgetRouteUnary : UnaryHistory budgetRoute :=
    unary_cont_closed budgetWindowsUnary realWindowUnary budgetRealWindow
  have realRouteUnary : UnaryHistory realRoute :=
    unary_cont_closed budgetRouteUnary localNameUnary budgetLocalName
  exact
    ⟨sourceUnary, selectedUnary, omittedUnary, budgetWindowsUnary, realRouteUnary,
      sourceSelected, ledgerOmitted, selectedBudget, budgetRealWindow, budgetLocalName,
      provenancePkg, realRoutePkg⟩

theorem ObserverFilterCarrier_real_window_synchronizer_handoff [AskSetup] [PackageSetup]
    {source selected omitted transport ledger routes provenance localName budgetSchedule
      budgetWindows synchronizerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
        bundle pkg ->
      UnaryHistory budgetSchedule ->
        UnaryHistory synchronizerRead ->
          Cont selected budgetSchedule budgetWindows ->
            Cont budgetWindows localName synchronizerRead ->
              PkgSig bundle synchronizerRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    ObserverFilterCarrier source selected omitted transport ledger routes
                        provenance localName bundle pkg ∧
                      hsame row budgetWindows)
                  (fun row : BHist =>
                    Cont selected budgetSchedule budgetWindows ∧
                      Cont budgetWindows localName synchronizerRead ∧
                        hsame row budgetWindows ∧ PkgSig bundle synchronizerRead pkg)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle synchronizerRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert
  intro carrier budgetScheduleUnary _synchronizerUnary selectedBudget budgetLocalName
    synchronizerPkg
  obtain ⟨sourceUnary, selectedUnary, omittedUnary, ledgerUnary, routesUnary,
    provenanceUnary, localNameUnary, sourceSelected, ledgerOmitted, routesLocalName,
    provenancePkg⟩ := carrier
  have budgetWindowsUnary : UnaryHistory budgetWindows :=
    unary_cont_closed selectedUnary budgetScheduleUnary selectedBudget
  have carrierWitness :
      ObserverFilterCarrier source selected omitted transport ledger routes provenance localName
          bundle pkg :=
    ⟨sourceUnary, selectedUnary, omittedUnary, ledgerUnary, routesUnary, provenanceUnary,
      localNameUnary, sourceSelected, ledgerOmitted, routesLocalName, provenancePkg⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro budgetWindows
          (And.intro carrierWitness (hsame_refl budgetWindows))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceData
        exact And.intro sourceData.left
          (hsame_trans (hsame_symm sameRows) sourceData.right)
    }
    pattern_sound := by
      intro row sourceData
      exact ⟨selectedBudget, budgetLocalName, sourceData.right, synchronizerPkg⟩
    ledger_sound := by
      intro row sourceData
      exact
        ⟨unary_transport budgetWindowsUnary (hsame_symm sourceData.right), provenancePkg,
          synchronizerPkg⟩
  }

end BEDC.Derived.ObserverFilterUp
