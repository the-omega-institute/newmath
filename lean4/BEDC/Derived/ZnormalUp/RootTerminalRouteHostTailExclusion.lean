import BEDC.Derived.ZnormalUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootTerminalRouteHostTailExclusion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRoute hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal terminalRoute →
          PkgSig bundle terminalRoute pkg →
            hsame terminalRead terminal ∧ hsame terminalRoute continuation ∧
              UnaryHistory terminalRead ∧ UnaryHistory terminalRoute ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRoute pkg ∧
                  (Cont terminalRoute (BHist.e0 hostTail) terminalRead → False) ∧
                    (Cont terminalRoute (BHist.e1 hostTail) terminalRead → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet typedFuelTerminalRead terminalReadNormalTerminalRoute terminalRoutePkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalRouteSame : hsame terminalRoute continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal)
      terminalReadNormalTerminalRoute terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalTerminalRoute
  exact
    ⟨terminalReadSame, terminalRouteSame, terminalReadUnary, terminalRouteUnary,
      provenancePkg, terminalRoutePkg,
      cont_mutual_extension_right_tail_absurd.left terminalReadNormalTerminalRoute,
      cont_mutual_extension_right_tail_absurd.right terminalReadNormalTerminalRoute⟩

end BEDC.Derived.ZnormalUp
