import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_consumer_packet_totality [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' zeroRead criticalRead publicRoot :
        BHist}
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
                        Cont routes name zeroRead →
                          Cont routes name criticalRead →
                            Cont routes name publicRoot →
                              PkgSig bundle zeroRead pkg →
                                PkgSig bundle criticalRead pkg →
                                  PkgSig bundle publicRoot pkg →
                                    hsame analytic analytic' ∧
                                      hsame transports transports' ∧
                                        hsame provenance provenance' ∧
                                          hsame gamma gamma' ∧ UnaryHistory zeroRead ∧
                                            UnaryHistory criticalRead ∧
                                              UnaryHistory publicRoot ∧
                                                hsame zeroRead (append routes name) ∧
                                                  hsame criticalRead (append routes name) ∧
                                                    hsame publicRoot (append routes name) ∧
                                                      PkgSig bundle name pkg ∧
                                                        PkgSig bundle provenance' pkg ∧
                                                          PkgSig bundle zeroRead pkg ∧
                                                            PkgSig bundle criticalRead pkg ∧
                                                              PkgSig bundle publicRoot pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary zeroRoute criticalRoute publicRoute zeroPkg
    criticalPkg publicPkg
  have zeroReadiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := zeroRead)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary zeroRoute
  obtain ⟨analyticSame, transportsSame, provenanceSame, gammaSame, zeroUnary, zeroSame,
    namePkg, provenancePkg'⟩ := zeroReadiness
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed routesUnary nameUnary criticalRoute
  have publicUnary : UnaryHistory publicRoot :=
    unary_cont_closed routesUnary nameUnary publicRoute
  exact
    ⟨analyticSame, transportsSame, provenanceSame, gammaSame, zeroUnary, criticalUnary,
      publicUnary, zeroSame, criticalRoute, publicRoute, namePkg, provenancePkg', zeroPkg,
      criticalPkg, publicPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
