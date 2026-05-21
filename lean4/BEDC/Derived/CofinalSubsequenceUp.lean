import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalSubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CofinalSubsequenceCarrier [AskSetup] [PackageSetup]
    (source selector window dyadic regseq realSeal transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory selector ∧ UnaryHistory window ∧
    UnaryHistory dyadic ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont source selector window ∧
          Cont window dyadic transport ∧ Cont regseq dyadic realSeal ∧
            Cont realSeal provenance nameCert ∧ hsame realSeal (append regseq dyadic) ∧
              PkgSig bundle provenance pkg

theorem CofinalSubsequenceCarrier_regseqrat_consumer_boundary [AskSetup] [PackageSetup]
    {source selector window dyadic regseq realSeal transport route provenance nameCert
      consumerRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
        provenance nameCert bundle pkg ->
      Cont regseq realSeal sealRead ->
        Cont sealRead consumerRead route ->
          UnaryHistory sealRead ∧ UnaryHistory route ∧ hsame realSeal (append regseq dyadic) ∧
            PkgSig bundle provenance pkg := by
  intro carrier sealReadRow _consumerRoute
  obtain ⟨_sourceUnary, _selectorUnary, _windowUnary, _dyadicUnary, regseqUnary,
    realSealUnary, _transportUnary, routeUnary, _provenanceUnary, _nameCertUnary,
    _sourceSelectorWindow, _windowDyadicTransport, _regseqDyadicSeal,
    _sealProvenanceNameCert, sealSame, pkgSig⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary realSealUnary sealReadRow
  exact ⟨sealReadUnary, routeUnary, sealSame, pkgSig⟩

theorem CofinalSubsequenceCarrier_window_handoff_exactness [AskSetup] [PackageSetup]
    {source selector window dyadic regseq realSeal transport route provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
        provenance nameCert bundle pkg ->
      Cont (append source selector) dyadic transport ∧
        hsame transport (append (append source selector) dyadic) ∧
          Cont regseq dyadic realSeal ∧ PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_sourceUnary, _selectorUnary, _windowUnary, _dyadicUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    sourceSelectorWindow, windowDyadicTransport, regseqDyadicSeal, _sealProvenanceNameCert,
    _sealSame, pkgSig⟩ := carrier
  cases sourceSelectorWindow
  cases windowDyadicTransport
  exact ⟨rfl, rfl, regseqDyadicSeal, pkgSig⟩

theorem CofinalSubsequenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source selector window dyadic regseq realSeal transport route provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
      provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
            provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
            provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
            provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist CofinalSubsequenceCarrier hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro nameCert (And.intro carrier (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem CofinalSubsequenceCarrier_selector_transport_exactness [AskSetup] [PackageSetup]
    {source selector window dyadic regseq realSeal transport route provenance nameCert
      source' selector' window' dyadic' regseq' realSeal' transport' route' provenance'
      nameCert' consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
        provenance nameCert bundle pkg ->
      CofinalSubsequenceCarrier source' selector' window' dyadic' regseq' realSeal' transport'
        route' provenance' nameCert' bundle pkg ->
        hsame source source' ->
          hsame selector selector' ->
            hsame window window' ->
              hsame dyadic dyadic' ->
                hsame regseq regseq' ->
                  hsame realSeal realSeal' ->
                    hsame transport transport' ->
                      hsame route route' ->
                        hsame provenance provenance' ->
                          hsame nameCert nameCert' ->
                            Cont route consumerRead nameCert ->
                              UnaryHistory consumerRead ∧
                                hsame (append source selector) (append source' selector') ∧
                                  hsame (append window dyadic) (append window' dyadic') ∧
                                    hsame (append regseq realSeal)
                                      (append regseq' realSeal') ∧
                                      PkgSig bundle provenance pkg := by
  intro carrier carrier' sameSource sameSelector sameWindow sameDyadic sameRegseq
    sameRealSeal _sameTransport _sameRoute _sameProvenance _sameNameCert consumerRow
  obtain ⟨_sourceUnary, _selectorUnary, _windowUnary, _dyadicUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, nameCertUnary,
    _sourceSelectorWindow, _windowDyadicTransport, _regseqDyadicSeal, _sealProvenanceNameCert,
    _sealSame, pkgSig⟩ := carrier
  obtain ⟨_sourceUnary', _selectorUnary', _windowUnary', _dyadicUnary', _regseqUnary',
    _realSealUnary', _transportUnary', _routeUnary', _provenanceUnary', _nameCertUnary',
    _sourceSelectorWindow', _windowDyadicTransport', _regseqDyadicSeal',
    _sealProvenanceNameCert', _sealSame', _pkgSig'⟩ := carrier'
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_right_factor consumerRow nameCertUnary
  have sourceSelectorSame : hsame (append source selector) (append source' selector') :=
    cont_respects_hsame sameSource sameSelector (cont_intro rfl) (cont_intro rfl)
  have windowDyadicSame : hsame (append window dyadic) (append window' dyadic') :=
    cont_respects_hsame sameWindow sameDyadic (cont_intro rfl) (cont_intro rfl)
  have regseqRealSealSame : hsame (append regseq realSeal) (append regseq' realSeal') :=
    cont_respects_hsame sameRegseq sameRealSeal (cont_intro rfl) (cont_intro rfl)
  exact ⟨consumerUnary, sourceSelectorSame, windowDyadicSame, regseqRealSealSame, pkgSig⟩

theorem CofinalSubsequenceCarrier_public_export_package [AskSetup] [PackageSetup]
    {source selector window dyadic regseq realSeal transport route provenance nameCert
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
        provenance nameCert bundle pkg ->
      Cont nameCert downstream provenance ->
        SemanticNameCert
          (fun row : BHist =>
            CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport
              route provenance nameCert bundle pkg ∧ hsame row nameCert)
          (fun row : BHist =>
            CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport
              route provenance nameCert bundle pkg ∧ hsame row nameCert)
          (fun row : BHist =>
            CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport
              route provenance nameCert bundle pkg ∧ hsame row nameCert)
          hsame ∧
          UnaryHistory downstream ∧ hsame realSeal (append regseq dyadic) ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist CofinalSubsequenceCarrier hsame SemanticNameCert
  intro carrier nameCertDownstream
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport
            route provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport
            route provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport
            route provenance nameCert bundle pkg ∧ hsame row nameCert)
          hsame :=
      CofinalSubsequenceCarrier_namecert_obligations carrier
  obtain ⟨_sourceUnary, _selectorUnary, _windowUnary, _dyadicUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _nameCertUnary,
    _sourceSelectorWindow, _windowDyadicTransport, _regseqDyadicSeal,
    _sealProvenanceNameCert, sealSame, pkgSig⟩ := carrier
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_right_factor nameCertDownstream provenanceUnary
  exact ⟨cert, downstreamUnary, sealSame, pkgSig⟩

theorem CofinalSubsequenceCarrier_bridge_selector_schema [AskSetup] [PackageSetup]
    {source selector window dyadic regseq realSeal transport route provenance nameCert
      downstream bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalSubsequenceCarrier source selector window dyadic regseq realSeal transport route
        provenance nameCert bundle pkg ->
      Cont nameCert downstream provenance ->
        Cont downstream realSeal bridge ->
          PkgSig bundle bridge pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  CofinalSubsequenceCarrier source selector window dyadic regseq realSeal
                    transport route provenance nameCert bundle pkg ∧ hsame row nameCert)
                (fun row : BHist =>
                  CofinalSubsequenceCarrier source selector window dyadic regseq realSeal
                    transport route provenance nameCert bundle pkg ∧ hsame row nameCert)
                (fun row : BHist =>
                  CofinalSubsequenceCarrier source selector window dyadic regseq realSeal
                    transport route provenance nameCert bundle pkg ∧ hsame row nameCert)
                hsame ∧
              UnaryHistory downstream ∧ UnaryHistory bridge ∧
                hsame realSeal (append regseq dyadic) ∧ Cont downstream realSeal bridge ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg := by
  -- BEDC touchpoint anchor: BHist CofinalSubsequenceCarrier hsame SemanticNameCert
  intro carrier nameCertDownstream downstreamRealBridge bridgePkg
  have publicSurface :=
    CofinalSubsequenceCarrier_public_export_package carrier nameCertDownstream
  obtain ⟨certSurface, downstreamUnary, sealSame, provenancePkg⟩ := publicSurface
  obtain ⟨_sourceUnary, _selectorUnary, _windowUnary, _dyadicUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _sourceSelectorWindow, _windowDyadicTransport, _regseqDyadicSeal,
    _sealProvenanceNameCert, _sealSame, _pkgSig⟩ := carrier
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed downstreamUnary realSealUnary downstreamRealBridge
  exact
    ⟨certSurface,
      downstreamUnary,
      bridgeUnary,
      sealSame,
      downstreamRealBridge,
      provenancePkg,
      bridgePkg⟩

end BEDC.Derived.CofinalSubsequenceUp
