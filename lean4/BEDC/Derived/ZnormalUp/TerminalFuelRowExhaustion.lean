import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_fuel_row_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead refusal readback siblingRead joined : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal continuationRead ->
          Cont terminal normal refusal ->
            Cont refusal continuation readback ->
              Cont normal continuation siblingRead ->
                Cont terminalRead siblingRead joined ->
                  PkgSig bundle continuationRead pkg ->
                    PkgSig bundle readback pkg ->
                      PkgSig bundle siblingRead pkg ->
                        PkgSig bundle joined pkg ->
                          hsame terminalRead terminal ∧ UnaryHistory continuationRead ∧
                            UnaryHistory refusal ∧ UnaryHistory readback ∧
                              UnaryHistory siblingRead ∧ UnaryHistory joined ∧
                                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalContinuation terminalNormalRefusal
    refusalContinuationReadback normalContinuationSibling terminalReadSiblingJoined
    _continuationReadPkg _readbackPkg _siblingReadPkg _joinedPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalContinuation
  have refusalUnary : UnaryHistory refusal :=
    unary_cont_closed terminalUnary normalUnary terminalNormalRefusal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed refusalUnary continuationUnary refusalContinuationReadback
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSibling
  have joinedUnary : UnaryHistory joined :=
    unary_cont_closed terminalReadUnary siblingReadUnary terminalReadSiblingJoined
  exact
    ⟨terminalReadSame, continuationReadUnary, refusalUnary, readbackUnary,
      siblingReadUnary, joinedUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
