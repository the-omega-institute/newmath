import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_source_route_scoped_totality [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name etaPrime
      analyticPrime transportsPrime provenancePrime zeroLedgerPrime gammaPrime sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg →
      Cont basic etaPrime analyticPrime →
        Cont analyticPrime functional transportsPrime →
          Cont transportsPrime routes provenancePrime →
            Cont pole zeroLedgerPrime gammaPrime →
              PkgSig bundle provenancePrime pkg →
                hsame eta etaPrime →
                  hsame zeroLedger zeroLedgerPrime →
                    UnaryHistory routes →
                      UnaryHistory name →
                        Cont routes name sourceRead →
                          PkgSig bundle sourceRead pkg →
                            hsame analytic analyticPrime ∧
                              hsame transports transportsPrime ∧
                                hsame provenance provenancePrime ∧
                                  hsame gamma gammaPrime ∧
                                    UnaryHistory sourceRead ∧
                                      hsame sourceRead (append routes name) ∧
                                        Cont basic etaPrime analyticPrime ∧
                                          Cont analyticPrime functional transportsPrime ∧
                                            Cont transportsPrime routes provenancePrime ∧
                                              Cont pole zeroLedgerPrime gammaPrime ∧
                                                PkgSig bundle name pkg ∧
                                                  PkgSig bundle provenancePrime pkg ∧
                                                    PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary sourceRoute sourcePkg
  have ledger :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := etaPrime) (analytic' := analyticPrime)
      (transports' := transportsPrime) (provenance' := provenancePrime)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      provenancePkg etaSame
  obtain ⟨analyticSame, transportsSame, provenanceSame, namePkg, provenancePkg'⟩ := ledger
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedgerPrime) (gamma' := gammaPrime)
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, _namePkgGamma, _provenancePkgGamma⟩ := gammaBoundary
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed routesUnary nameUnary sourceRoute
  exact
    ⟨analyticSame, transportsSame, provenanceSame, gammaSame, sourceUnary, sourceRoute,
      basicRoute, functionalRoute, provenanceRoute, gammaRoute, namePkg, provenancePkg',
      sourcePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
