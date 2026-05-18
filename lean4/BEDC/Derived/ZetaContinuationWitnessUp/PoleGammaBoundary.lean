import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_pole_gamma_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedger' gamma' _poleRead gammaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont pole zeroLedger' gamma' ->
        hsame zeroLedger zeroLedger' ->
          UnaryHistory routes ->
            UnaryHistory name ->
              Cont routes name gammaRead ->
                Cont pole gamma gammaRead ->
                  PkgSig bundle gammaRead pkg ->
                    hsame gamma gamma' ∧ UnaryHistory gammaRead ∧
                      Cont pole zeroLedger' gamma' ∧ Cont routes name gammaRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle gammaRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame UnaryHistory
  intro packet gammaRoute zeroLedgerSame routesUnary nameUnary routesNameGamma _poleGammaRead
    gammaReadPkg
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedger') (gamma' := gamma')
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, _namePkg, provenancePkg⟩ := gammaBoundary
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed routesUnary nameUnary routesNameGamma
  exact
    ⟨gammaSame, gammaReadUnary, gammaRoute, routesNameGamma, provenancePkg,
      gammaReadPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
