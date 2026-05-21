import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_route_carrier_admission [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      etaPrime analyticPrime transportsPrime provenancePrime publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont basic etaPrime analyticPrime →
        Cont analyticPrime functional transportsPrime →
          Cont transportsPrime routes provenancePrime →
            hsame eta etaPrime →
              PkgSig bundle provenancePrime pkg →
                UnaryHistory routes →
                  UnaryHistory name →
                    Cont routes name publicRead →
                      PkgSig bundle publicRead pkg →
                        hsame analytic analyticPrime ∧ hsame transports transportsPrime ∧
                          hsame provenance provenancePrime ∧ UnaryHistory publicRead ∧
                            hsame publicRead (append routes name) ∧
                              Cont transportsPrime routes provenancePrime ∧
                                PkgSig bundle name pkg ∧
                                  PkgSig bundle provenancePrime pkg ∧
                                    PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute etaSame provenancePkg routesUnary
    nameUnary publicRoute publicPkg
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := etaPrime) (analytic' := analyticPrime)
      (transports' := transportsPrime) (provenance' := provenancePrime)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      provenancePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, namePkg, provenancePkg'⟩ :=
    ledger
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routesUnary nameUnary publicRoute
  exact
    ⟨analyticSame, transportsSame, provenanceSame, publicUnary, publicRoute,
      provenanceRoute, namePkg, provenancePkg', publicPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
