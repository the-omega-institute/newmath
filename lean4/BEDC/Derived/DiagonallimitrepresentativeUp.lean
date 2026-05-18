import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonallimitrepresentativeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.DiagonallimitrepresentativeUp
