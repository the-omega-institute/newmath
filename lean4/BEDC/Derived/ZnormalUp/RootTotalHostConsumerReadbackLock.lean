import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_total_host_consumer_readback_lock [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      totalHostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal totalHostRead ->
          PkgSig bundle totalHostRead pkg ->
            hsame terminalRead terminal ∧ hsame totalHostRead continuation ∧
              UnaryHistory terminalRead ∧ UnaryHistory totalHostRead ∧
                Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle totalHostRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet typedFuelTerminalRead terminalReadNormalTotalHost totalHostPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have totalHostSame : hsame totalHostRead continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal)
      terminalReadNormalTotalHost terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have totalHostUnary : UnaryHistory totalHostRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalTotalHost
  exact
    ⟨terminalReadSame, totalHostSame, terminalReadUnary, totalHostUnary,
      typedFuelTerminal, terminalNormalContinuation, namePkg, provenancePkg, totalHostPkg⟩

end BEDC.Derived.ZnormalUp
