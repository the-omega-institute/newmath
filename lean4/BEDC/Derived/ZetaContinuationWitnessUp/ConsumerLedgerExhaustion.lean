import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessConsumerLedgerExhaustion [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroRead criticalRead gammaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name zeroRead ->
            Cont routes name criticalRead ->
              Cont routes name gammaRead ->
                PkgSig bundle zeroRead pkg ->
                  PkgSig bundle criticalRead pkg ->
                    PkgSig bundle gammaRead pkg ->
                      UnaryHistory zeroRead ∧ UnaryHistory criticalRead ∧
                        UnaryHistory gammaRead ∧ hsame zeroRead (append routes name) ∧
                          hsame criticalRead (append routes name) ∧
                            hsame gammaRead (append routes name) ∧ Cont basic eta analytic ∧
                              Cont analytic functional transports ∧
                                Cont pole zeroLedger gamma ∧
                                  Cont transports routes provenance ∧
                                    PkgSig bundle name pkg ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle zeroRead pkg ∧
                                          PkgSig bundle criticalRead pkg ∧
                                            PkgSig bundle gammaRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet routesUnary nameUnary zeroRoute criticalRoute gammaRoute zeroPkg criticalPkg
    gammaPkg
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed routesUnary nameUnary zeroRoute
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed routesUnary nameUnary criticalRoute
  have gammaUnary : UnaryHistory gammaRead :=
    unary_cont_closed routesUnary nameUnary gammaRoute
  exact
    ⟨zeroUnary, criticalUnary, gammaUnary, zeroRoute, criticalRoute, gammaRoute,
      basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
      transportsRoutesProvenance, namePkg, provenancePkg, zeroPkg, criticalPkg, gammaPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
