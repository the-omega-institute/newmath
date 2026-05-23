import BEDC.Derived.ZetaContinuationWitnessUp.ClassifierStability

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessRouteClassifierStability [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' zeroLedger' gamma' provenance' routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta' analytic' ->
        Cont analytic' functional transports' ->
          Cont pole zeroLedger' gamma' ->
            Cont transports' routes provenance' ->
              PkgSig bundle provenance' pkg ->
                hsame eta eta' ->
                  hsame zeroLedger zeroLedger' ->
                    UnaryHistory routes ->
                      UnaryHistory name ->
                        Cont routes name routeRead ->
                          hsame analytic analytic' ∧ hsame transports transports' ∧
                            hsame gamma gamma' ∧ hsame provenance provenance' ∧
                              UnaryHistory routeRead ∧
                                hsame routeRead (append routes name) ∧
                                  PkgSig bundle name pkg ∧
                                    PkgSig bundle provenance' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute gammaRoute provenanceRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary routesNameRead
  have classifier :=
    ZetaContinuationWitnessPacket_classifier_stability
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (zeroLedger' := zeroLedger') (gamma' := gamma')
      (provenance' := provenance') (bundle := bundle) (pkg := pkg) packet basicRoute
      functionalRoute gammaRoute provenanceRoute provenancePkg etaSame zeroLedgerSame
  obtain ⟨analyticSame, transportsSame, gammaSame, provenanceSame, namePkg,
    provenancePkg'⟩ := classifier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed routesUnary nameUnary routesNameRead
  exact
    ⟨analyticSame, transportsSame, gammaSame, provenanceSame, routeUnary, routesNameRead,
      namePkg, provenancePkg'⟩

end BEDC.Derived.ZetaContinuationWitnessUp
