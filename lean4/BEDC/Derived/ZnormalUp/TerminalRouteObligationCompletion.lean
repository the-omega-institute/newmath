import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTerminalRouteObligationCompletion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRoute siblingRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal terminalRoute →
          Cont normal continuation siblingRead →
            Cont siblingRead transports downstream →
              PkgSig bundle terminalRoute pkg →
                PkgSig bundle siblingRead pkg →
                  PkgSig bundle downstream pkg →
                    hsame terminalRead terminal ∧ hsame terminalRoute continuation ∧
                      UnaryHistory terminalRead ∧ UnaryHistory terminalRoute ∧
                        UnaryHistory siblingRead ∧ UnaryHistory downstream ∧
                          Cont typed fuel terminalRead ∧
                            Cont terminalRead normal terminalRoute ∧
                              Cont normal continuation siblingRead ∧
                                Cont siblingRead transports downstream ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle terminalRoute pkg ∧
                                      PkgSig bundle siblingRead pkg ∧
                                        PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet typedFuelTerminalRead terminalReadNormalRoute
    normalContinuationSibling siblingTransportsDownstream terminalRoutePkg siblingReadPkg
    downstreamPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalRouteSame : hsame terminalRoute continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal) terminalReadNormalRoute
      terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRoute
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSibling
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed siblingReadUnary transportsUnary siblingTransportsDownstream
  exact
    ⟨terminalReadSame, terminalRouteSame, terminalReadUnary, terminalRouteUnary,
      siblingReadUnary, downstreamUnary, typedFuelTerminalRead, terminalReadNormalRoute,
      normalContinuationSibling, siblingTransportsDownstream, provenancePkg, terminalRoutePkg,
      siblingReadPkg, downstreamPkg⟩

end BEDC.Derived.ZnormalUp
