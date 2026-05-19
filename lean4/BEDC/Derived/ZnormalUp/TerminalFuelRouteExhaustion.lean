import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_fuel_route_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal continuationRead →
          Cont continuationRead transports downstream →
            PkgSig bundle downstream pkg →
              hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                UnaryHistory continuationRead ∧ UnaryHistory downstream ∧
                  Cont terminalRead normal continuationRead ∧
                    Cont continuationRead transports downstream ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet typedFuelTerminalRead terminalReadNormalContinuationRead
    continuationReadTransportsDownstream downstreamPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed continuationReadUnary transportsUnary continuationReadTransportsDownstream
  exact
    ⟨terminalReadSame, terminalReadUnary, continuationReadUnary, downstreamUnary,
      terminalReadNormalContinuationRead, continuationReadTransportsDownstream, provenancePkg,
      downstreamPkg⟩

theorem ZnormalPacket_normal_word_sibling_separation [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name siblingRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation siblingRead →
        PkgSig bundle siblingRead pkg →
          UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory siblingRead ∧
            Cont normal continuation siblingRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle siblingRead pkg ∧ hsame siblingRead (append normal continuation) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet normalContinuationSiblingRead siblingReadPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSiblingRead
  exact
    ⟨normalUnary, continuationUnary, siblingReadUnary, normalContinuationSiblingRead,
      provenancePkg, siblingReadPkg, normalContinuationSiblingRead⟩

end BEDC.Derived.ZnormalUp
