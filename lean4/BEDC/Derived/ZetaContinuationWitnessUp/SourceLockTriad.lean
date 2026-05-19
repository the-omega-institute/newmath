import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_source_lock_triad [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name etaPrime
      analyticPrime transportsPrime publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont basic etaPrime analyticPrime →
        Cont analyticPrime functional transportsPrime →
          hsame eta etaPrime →
            UnaryHistory routes →
              UnaryHistory name →
                Cont routes name publicRead →
                  PkgSig bundle publicRead pkg →
                    hsame analytic analyticPrime ∧ hsame transports transportsPrime ∧
                      UnaryHistory publicRead ∧ hsame publicRead (append routes name) ∧
                        Cont basic etaPrime analyticPrime ∧
                          Cont analyticPrime functional transportsPrime ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute etaSame routesUnary nameUnary publicRoute publicPkg
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, _provenancePkg⟩ := packet
  have analyticSame : hsame analytic analyticPrime :=
    cont_respects_hsame (hsame_refl basic) etaSame basicEtaAnalytic basicRoute
  have transportsSame : hsame transports transportsPrime :=
    cont_respects_hsame analyticSame (hsame_refl functional) analyticFunctionalTransports
      functionalRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routesUnary nameUnary publicRoute
  exact
    ⟨analyticSame, transportsSame, publicUnary, publicRoute, basicRoute, functionalRoute,
      namePkg, publicPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
