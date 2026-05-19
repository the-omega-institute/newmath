import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_critical_strip_route_separation
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' criticalRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont basic eta' analytic' →
        Cont analytic' functional transports' →
          Cont transports' routes provenance' →
            Cont pole zeroLedger' gamma' →
              PkgSig bundle provenance' pkg →
                hsame eta eta' →
                  hsame zeroLedger zeroLedger' →
                    UnaryHistory routes →
                      UnaryHistory name →
                        Cont routes name criticalRead →
                          Cont routes name publicRead →
                            PkgSig bundle criticalRead pkg →
                              hsame analytic analytic' ∧ hsame transports transports' ∧
                                hsame provenance provenance' ∧ hsame gamma gamma' ∧
                                  hsame criticalRead publicRead ∧
                                    UnaryHistory criticalRead ∧ UnaryHistory publicRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle provenance' pkg ∧
                                          PkgSig bundle criticalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary criticalRoute publicRoute criticalPkg
  have readiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := criticalRead)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary criticalRoute
  obtain ⟨analyticSame, transportsSame, provenanceSame, gammaSame, criticalUnary,
    _criticalAppend, namePkg, provenancePkg'⟩ := readiness
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routesUnary nameUnary publicRoute
  have criticalPublicSame : hsame criticalRead publicRead :=
    cont_respects_hsame (hsame_refl routes) (hsame_refl name) criticalRoute publicRoute
  exact
    ⟨analyticSame, transportsSame, provenanceSame, gammaSame, criticalPublicSame,
      criticalUnary, publicUnary, namePkg, provenancePkg', criticalPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
