import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonallimitrepresentativeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalLimitRepresentativeCarrier [AskSetup] [PackageSetup]
    (family modulus request selectedFamilyIndex selectedReadbackIndex window readback ledger
      realSeal transport continuation provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory request ∧
    UnaryHistory selectedFamilyIndex ∧ UnaryHistory selectedReadbackIndex ∧
      UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory ledger ∧
        UnaryHistory realSeal ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont modulus request selectedFamilyIndex ∧
            Cont window readback selectedReadbackIndex ∧
              Cont ledger realSeal transport ∧
                Cont transport continuation provenance ∧ PkgSig bundle localName pkg

theorem DiagonalLimitRepresentativeNameCertObligations [AskSetup] [PackageSetup]
    {family modulus request selectedFamilyIndex selectedReadbackIndex window readback ledger
      realSeal transport continuation provenance localName routeRead indexRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitRepresentativeCarrier family modulus request selectedFamilyIndex
        selectedReadbackIndex window readback ledger realSeal transport continuation provenance
        localName bundle pkg ->
      Cont modulus request indexRead ->
        Cont window readback terminalRead ->
          Cont ledger realSeal routeRead ->
            PkgSig bundle localName pkg ->
              UnaryHistory family /\ UnaryHistory modulus /\ UnaryHistory request /\
                UnaryHistory selectedFamilyIndex /\ UnaryHistory selectedReadbackIndex /\
                  UnaryHistory window /\ UnaryHistory readback /\ UnaryHistory ledger /\
                    UnaryHistory realSeal /\ UnaryHistory indexRead /\
                      UnaryHistory terminalRead /\ UnaryHistory routeRead /\
                        Cont modulus request indexRead /\ Cont window readback terminalRead /\
                          Cont ledger realSeal routeRead /\ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier modulusRequestIndex windowReadbackTerminal ledgerSealRoute localPkg
  obtain ⟨familyUnary, modulusUnary, requestUnary, selectedFamilyUnary,
    selectedReadbackUnary, windowUnary, readbackUnary, ledgerUnary, realSealUnary,
    _provenanceUnary, _localNameUnary, _modulusRequestSelected,
    _windowReadbackSelected, _ledgerSealTransport, _transportContinuationProvenance,
    _carrierPkg⟩ := carrier
  have indexReadUnary : UnaryHistory indexRead :=
    unary_cont_closed modulusUnary requestUnary modulusRequestIndex
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed windowUnary readbackUnary windowReadbackTerminal
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerSealRoute
  exact
    ⟨familyUnary, modulusUnary, requestUnary, selectedFamilyUnary, selectedReadbackUnary,
      windowUnary, readbackUnary, ledgerUnary, realSealUnary, indexReadUnary,
      terminalReadUnary, routeReadUnary, modulusRequestIndex, windowReadbackTerminal,
      ledgerSealRoute, localPkg⟩

theorem DiagonalLimitRepresentativeCarrier_route_read_consumer_boundary [AskSetup] [PackageSetup]
    {family modulus request selectedFamilyIndex selectedReadbackIndex window readback ledger
      realSeal transport continuation provenance localName indexRead terminalRead routeRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitRepresentativeCarrier family modulus request selectedFamilyIndex
        selectedReadbackIndex window readback ledger realSeal transport continuation provenance
        localName bundle pkg ->
      Cont modulus request indexRead ->
        Cont window readback terminalRead ->
          Cont ledger realSeal routeRead ->
            Cont routeRead continuation consumer ->
              PkgSig bundle consumer pkg ->
                UnaryHistory indexRead ∧ UnaryHistory terminalRead ∧ UnaryHistory routeRead ∧
                  UnaryHistory consumer ∧ Cont modulus request indexRead ∧
                    Cont window readback terminalRead ∧ Cont ledger realSeal routeRead ∧
                      Cont routeRead continuation consumer ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier modulusRequestIndex windowReadbackTerminal ledgerSealRoute routeConsumer
    consumerPkg
  have carrierForObligations := carrier
  obtain ⟨_familyUnary, _modulusUnary, _requestUnary, _selectedFamilyUnary,
    _selectedReadbackUnary, _windowUnary, _readbackUnary, _ledgerUnary, _realSealUnary,
    provenanceUnary, _localNameUnary, _modulusRequestSelected, _windowReadbackSelected,
    _ledgerSealTransport, transportContinuationProvenance, localPkg⟩ := carrier
  have obligations :=
    DiagonalLimitRepresentativeNameCertObligations
      (family := family) (modulus := modulus) (request := request)
      (selectedFamilyIndex := selectedFamilyIndex)
      (selectedReadbackIndex := selectedReadbackIndex) (window := window)
      (readback := readback) (ledger := ledger) (realSeal := realSeal)
      (transport := transport) (continuation := continuation) (provenance := provenance)
      (localName := localName) (routeRead := routeRead) (indexRead := indexRead)
      (terminalRead := terminalRead) (bundle := bundle) (pkg := pkg) carrierForObligations
      modulusRequestIndex windowReadbackTerminal ledgerSealRoute localPkg
  obtain ⟨_familyRouteUnary, _modulusRouteUnary, _requestRouteUnary,
    _selectedFamilyRouteUnary, _selectedReadbackRouteUnary, _windowRouteUnary,
    _readbackRouteUnary, _ledgerRouteUnary, _realSealRouteUnary, indexReadUnary,
    terminalReadUnary, routeReadUnary, _modulusRequestRoute, _windowReadbackRoute,
    _ledgerSealRoute, _localRoutePkg⟩ := obligations
  have continuationUnary : UnaryHistory continuation :=
    unary_cont_right_factor transportContinuationProvenance provenanceUnary
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeReadUnary continuationUnary routeConsumer
  exact
    ⟨indexReadUnary, terminalReadUnary, routeReadUnary, consumerUnary, modulusRequestIndex,
      windowReadbackTerminal, ledgerSealRoute, routeConsumer, localPkg, consumerPkg⟩

theorem DiagonalLimitRepresentativeCarrier_pkg_namecert_source_closure [AskSetup] [PackageSetup]
    {family modulus request selectedFamilyIndex selectedReadbackIndex window readback ledger
      realSeal transport continuation provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitRepresentativeCarrier family modulus request selectedFamilyIndex
        selectedReadbackIndex window readback ledger realSeal transport continuation provenance
        localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist => hsame row localName)
          (fun row : BHist => hsame row localName ∧ Cont transport continuation provenance)
          hsame ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont transport continuation provenance ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier
  obtain ⟨_familyUnary, _modulusUnary, _requestUnary, _selectedFamilyUnary,
    _selectedReadbackUnary, _windowUnary, _readbackUnary, _ledgerUnary, _realSealUnary,
    provenanceUnary, localNameUnary, _modulusRequestSelected, _windowReadbackSelected,
    _ledgerSealTransport, transportContinuationProvenance, localPkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row localName ∧ UnaryHistory row)
        (fun row : BHist => hsame row localName)
        (fun row : BHist => hsame row localName ∧ Cont transport continuation provenance)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localName ⟨hsame_refl localName, localNameUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, transportContinuationProvenance⟩
    }
  exact ⟨cert, provenanceUnary, localNameUnary, transportContinuationProvenance, localPkg⟩

end BEDC.Derived.DiagonallimitrepresentativeUp
