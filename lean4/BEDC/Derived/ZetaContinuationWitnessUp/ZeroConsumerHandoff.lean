import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessZeroConsumerHandoff [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg ->
      Cont routes name zeroRead ->
        Cont zeroRead gamma publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory routes ->
              UnaryHistory name ->
                UnaryHistory gamma ->
                  UnaryHistory zeroRead ∧ UnaryHistory publicRead ∧
                    Cont routes name zeroRead ∧ Cont zeroRead gamma publicRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet routesNameZero zeroGammaPublic publicPkg routesUnary nameUnary gammaUnary
  obtain
    ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
      _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed routesUnary nameUnary routesNameZero
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed zeroUnary gammaUnary zeroGammaPublic
  exact
    ⟨zeroUnary, publicUnary, routesNameZero, zeroGammaPublic, namePkg, provenancePkg,
      publicPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
