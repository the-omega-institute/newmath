import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_gamma_public_boundary_lock
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedger' gamma' gammaRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont pole zeroLedger' gamma' ->
        hsame zeroLedger zeroLedger' ->
          UnaryHistory routes ->
            UnaryHistory name ->
              Cont routes name gammaRead ->
                PkgSig bundle gammaRead pkg ->
                  hsame gamma gamma' ∧ UnaryHistory gammaRead ∧
                    hsame gammaRead (append routes name) ∧ Cont pole zeroLedger' gamma' ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle gammaRead pkg ∧
                          (Cont gammaRead (BHist.e0 hostTail) routes -> False) ∧
                            (Cont gammaRead (BHist.e1 hostTail) routes -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet gammaRoute zeroLedgerSame routesUnary nameUnary routesNameGamma gammaPkg
  have gammaBoundary :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedger') (gamma' := gamma')
      (bundle := bundle) (pkg := pkg) packet gammaRoute zeroLedgerSame
  obtain ⟨gammaSame, namePkg, provenancePkg⟩ := gammaBoundary
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed routesUnary nameUnary routesNameGamma
  exact
    ⟨gammaSame, gammaReadUnary, routesNameGamma, gammaRoute, namePkg, provenancePkg,
      gammaPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left routesNameGamma hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right routesNameGamma hostReturn)⟩

end BEDC.Derived.ZetaContinuationWitnessUp
