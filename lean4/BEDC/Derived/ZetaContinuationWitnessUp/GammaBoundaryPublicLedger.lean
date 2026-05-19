import BEDC.Derived.ZetaContinuationWitnessUp.GammaBoundaryPublicExport

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessGammaBoundaryPublicLedger [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedgerPrime gammaPrime publicRead gammaPublic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont pole zeroLedgerPrime gammaPrime ->
        hsame zeroLedger zeroLedgerPrime ->
          UnaryHistory routes ->
            UnaryHistory name ->
              Cont routes name publicRead ->
                Cont functional gammaPrime gammaPublic ->
                  PkgSig bundle publicRead pkg ->
                    PkgSig bundle gammaPublic pkg ->
                      hsame gamma gammaPrime ∧ UnaryHistory publicRead ∧
                        hsame publicRead (append routes name) ∧
                          Cont pole zeroLedgerPrime gammaPrime ∧
                            Cont functional gammaPrime gammaPublic ∧
                              Cont transports routes provenance ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle publicRead pkg ∧
                                    PkgSig bundle gammaPublic pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet gammaRoute zeroLedgerSame routesUnary nameUnary routesNamePublic
    functionalGammaPublic publicPkg gammaPublicPkg
  have publicExport :=
    ZetaContinuationWitnessGammaBoundaryPublicExport
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedgerPrime := zeroLedgerPrime) (gammaPrime := gammaPrime)
      (publicRead := publicRead) (hostTail := BHist.Empty) (bundle := bundle) (pkg := pkg)
      packet gammaRoute zeroLedgerSame routesUnary nameUnary routesNamePublic publicPkg
  obtain ⟨gammaSame, publicUnary, publicSame, gammaRoute', transportsRoutesProvenance,
    namePkg, provenancePkg, publicPkg', _e0Lock, _e1Lock⟩ := publicExport
  exact
    ⟨gammaSame, publicUnary, publicSame, gammaRoute', functionalGammaPublic,
      transportsRoutesProvenance, namePkg, provenancePkg, publicPkg', gammaPublicPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
