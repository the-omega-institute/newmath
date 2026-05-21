import BEDC.Derived.DiagonallimitrepresentativeUp

namespace BEDC.Derived.DiagonallimitrepresentativeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitRepresentativeRootReadinessTriad [AskSetup] [PackageSetup]
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
                UnaryHistory modulus ∧ UnaryHistory request ∧ UnaryHistory indexRead ∧
                  UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory terminalRead ∧
                    UnaryHistory ledger ∧ UnaryHistory realSeal ∧ UnaryHistory routeRead ∧
                      UnaryHistory consumer ∧ Cont modulus request indexRead ∧
                        Cont window readback terminalRead ∧ Cont ledger realSeal routeRead ∧
                          Cont routeRead continuation consumer ∧ PkgSig bundle localName pkg ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier modulusRequestIndex windowReadbackTerminal ledgerSealRoute routeConsumer
    consumerPkg
  obtain ⟨_familyUnary, modulusUnary, requestUnary, _selectedFamilyUnary,
    _selectedReadbackUnary, windowUnary, readbackUnary, ledgerUnary, realSealUnary,
    provenanceUnary, _localNameUnary, _modulusRequestSelected, _windowReadbackSelected,
    _ledgerSealTransport, transportContinuationProvenance, localPkg⟩ := carrier
  have indexReadUnary : UnaryHistory indexRead :=
    unary_cont_closed modulusUnary requestUnary modulusRequestIndex
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed windowUnary readbackUnary windowReadbackTerminal
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerSealRoute
  have continuationUnary : UnaryHistory continuation :=
    unary_cont_right_factor transportContinuationProvenance provenanceUnary
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeReadUnary continuationUnary routeConsumer
  exact
    ⟨modulusUnary, requestUnary, indexReadUnary, windowUnary, readbackUnary,
      terminalReadUnary, ledgerUnary, realSealUnary, routeReadUnary, consumerUnary,
      modulusRequestIndex, windowReadbackTerminal, ledgerSealRoute, routeConsumer, localPkg,
      consumerPkg⟩

end BEDC.Derived.DiagonallimitrepresentativeUp
