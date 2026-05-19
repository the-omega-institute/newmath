import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessGammaBoundaryPublicExport [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedgerPrime gammaPrime publicRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont pole zeroLedgerPrime gammaPrime ->
        hsame zeroLedger zeroLedgerPrime ->
          UnaryHistory routes ->
            UnaryHistory name ->
              Cont routes name publicRead ->
                PkgSig bundle publicRead pkg ->
                  hsame gamma gammaPrime ∧ UnaryHistory publicRead ∧
                    hsame publicRead (append routes name) ∧
                      Cont pole zeroLedgerPrime gammaPrime ∧
                        Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                            (Cont publicRead (BHist.e0 hostTail) routes -> False) ∧
                              (Cont publicRead (BHist.e1 hostTail) routes -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet gammaRoute zeroLedgerSame routesUnary nameUnary routesNamePublic publicPkg
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedgerPrime) (gamma' := gammaPrime)
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, namePkg, provenancePkg⟩ := gammaBoundary
  obtain ⟨_basicAnalytic, _analyticTransport, _poleGamma, transportsRoutesProvenance,
    _namePkg, _provenancePkg⟩ := packet
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed routesUnary nameUnary routesNamePublic
  exact
    ⟨gammaSame, publicReadUnary, routesNamePublic, gammaRoute, transportsRoutesProvenance,
      namePkg, provenancePkg, publicPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left routesNamePublic hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right routesNamePublic hostReturn)⟩

theorem ZetaContinuationWitnessPacket_gamma_boundary_public_export [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedger' gamma' gammaPublic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont pole zeroLedger' gamma' →
        hsame zeroLedger zeroLedger' →
          Cont functional gamma' gammaPublic →
            PkgSig bundle gammaPublic pkg →
              hsame gamma gamma' ∧ Cont functional gamma' gammaPublic ∧
                Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle gammaPublic pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet gammaRoute zeroLedgerSame functionalGammaPublic gammaPublicPkg
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedger') (gamma' := gamma')
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, namePkg, provenancePkg⟩ := gammaBoundary
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    transportsRoutesProvenance, _namePkg, _provenancePkg⟩ := packet
  exact
    ⟨gammaSame, functionalGammaPublic, transportsRoutesProvenance, namePkg,
      provenancePkg, gammaPublicPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
