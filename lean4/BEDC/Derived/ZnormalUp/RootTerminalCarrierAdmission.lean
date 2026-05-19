import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_terminal_carrier_admission [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      rootRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal rootRead ->
          Cont rootRead transports downstream ->
            PkgSig bundle downstream pkg ->
              hsame terminalRead terminal ∧ hsame rootRead continuation ∧
                UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory normal ∧
                  UnaryHistory terminalRead ∧ UnaryHistory rootRead ∧
                    UnaryHistory downstream ∧ Cont typed fuel terminalRead ∧
                      Cont terminalRead normal rootRead ∧ Cont rootRead transports downstream ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRoot rootReadTransportsDownstream
    downstreamPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have rootReadSame : hsame rootRead continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal)
      terminalReadNormalRoot terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRoot
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed rootReadUnary transportsUnary rootReadTransportsDownstream
  exact
    ⟨terminalReadSame, rootReadSame, typedUnary, fuelUnary, normalUnary, terminalReadUnary,
      rootReadUnary, downstreamUnary, typedFuelTerminalRead, terminalReadNormalRoot,
      rootReadTransportsDownstream, namePkg, provenancePkg, downstreamPkg⟩

end BEDC.Derived.ZnormalUp
