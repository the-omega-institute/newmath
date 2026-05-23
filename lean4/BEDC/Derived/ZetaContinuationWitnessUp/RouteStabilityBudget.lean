import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_route_stability_budget [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' zeroLedger' gamma' routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg →
      Cont basic eta' analytic' →
      Cont analytic' functional transports' →
      Cont pole zeroLedger' gamma' →
      hsame eta eta' →
      hsame zeroLedger zeroLedger' →
      UnaryHistory routes →
      UnaryHistory name →
      Cont routes name routeRead →
      hsame analytic analytic' ∧ hsame transports transports' ∧ hsame gamma gamma' ∧
        UnaryHistory routeRead ∧ hsame routeRead (append routes name) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute gammaRoute etaSame zeroLedgerSame routesUnary
    nameUnary routesNameRead
  obtain ⟨basicAnalytic, analyticTransport, poleGamma, _transportProvenance, _namePkg,
    _provenancePkg⟩ := packet
  have analyticSame : hsame analytic analytic' :=
    cont_respects_hsame (hsame_refl basic) etaSame basicAnalytic basicRoute
  have transportsSame : hsame transports transports' :=
    cont_respects_hsame analyticSame (hsame_refl functional) analyticTransport functionalRoute
  have gammaSame : hsame gamma gamma' :=
    cont_respects_hsame (hsame_refl pole) zeroLedgerSame poleGamma gammaRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed routesUnary nameUnary routesNameRead
  exact ⟨analyticSame, transportsSame, gammaSame, routeUnary, routesNameRead⟩

end BEDC.Derived.ZetaContinuationWitnessUp
