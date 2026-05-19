import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalDownstreamReadinessObligationPackage [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead terminalRoute
      siblingRead downstream finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal terminalRoute →
          Cont normal continuation siblingRead →
            Cont siblingRead transports downstream →
              Cont downstream provenance finalRead →
                PkgSig bundle finalRead pkg →
                  UnaryHistory terminalRead ∧ UnaryHistory terminalRoute ∧
                    UnaryHistory siblingRead ∧ UnaryHistory downstream ∧
                      UnaryHistory finalRead ∧ hsame terminalRead terminal ∧
                        hsame terminalRoute continuation ∧ Cont typed fuel terminalRead ∧
                          Cont terminalRead normal terminalRoute ∧
                            Cont normal continuation siblingRead ∧
                              Cont siblingRead transports downstream ∧
                                Cont downstream provenance finalRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalTerminalRoute
    normalContinuationSiblingRead siblingReadTransportsDownstream downstreamProvenanceFinalRead
    finalReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalTerminalRoute
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSiblingRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed siblingReadUnary transportsUnary siblingReadTransportsDownstream
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed downstreamUnary provenanceUnary downstreamProvenanceFinalRead
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalRouteSame : hsame terminalRoute continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal) terminalReadNormalTerminalRoute
      terminalNormalContinuation
  exact
    ⟨terminalReadUnary, terminalRouteUnary, siblingReadUnary, downstreamUnary, finalReadUnary,
      terminalReadSame, terminalRouteSame, typedFuelTerminalRead,
      terminalReadNormalTerminalRoute, normalContinuationSiblingRead, siblingReadTransportsDownstream,
      downstreamProvenanceFinalRead, provenancePkg, finalReadPkg⟩

end BEDC.Derived.ZnormalUp
