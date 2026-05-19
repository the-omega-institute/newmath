import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_frontier_lock [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      totalHostRead locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal totalHostRead →
          Cont totalHostRead routes locked →
            PkgSig bundle locked pkg →
              hsame terminalRead terminal ∧ hsame totalHostRead continuation ∧
                UnaryHistory locked ∧ Cont totalHostRead routes locked ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle locked pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalTotalHostRead totalHostReadRoutesLocked
    lockedPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have totalHostReadSame : hsame totalHostRead continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal)
      terminalReadNormalTotalHostRead terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have totalHostReadUnary : UnaryHistory totalHostRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalTotalHostRead
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed totalHostReadUnary routesUnary totalHostReadRoutesLocked
  exact
    ⟨terminalReadSame, totalHostReadSame, lockedUnary, totalHostReadRoutesLocked,
      provenancePkg, lockedPkg⟩

end BEDC.Derived.ZnormalUp
