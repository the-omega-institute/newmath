import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_gamma_functional_boundary_totality
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroLedgerA zeroLedgerB gammaA gammaB gammaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont pole zeroLedgerA gammaA ->
        Cont pole zeroLedgerB gammaB ->
          hsame zeroLedger zeroLedgerA ->
            hsame zeroLedger zeroLedgerB ->
              UnaryHistory routes ->
                UnaryHistory name ->
                  Cont routes name gammaRead ->
                    PkgSig bundle gammaRead pkg ->
                      hsame gamma gammaA ∧ hsame gamma gammaB ∧ hsame gammaA gammaB ∧
                        UnaryHistory gammaRead ∧ hsame gammaRead (append routes name) ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle gammaRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet gammaRouteA gammaRouteB zeroLedgerSameA zeroLedgerSameB routesUnary
    nameUnary routesNameGamma gammaPkg
  have boundaryA :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedgerA) (gamma' := gammaA)
      (bundle := bundle) (pkg := pkg) packet gammaRouteA zeroLedgerSameA
  obtain ⟨gammaSameA, namePkg, provenancePkg⟩ := boundaryA
  have boundaryB :=
    ZetaContinuationWitnessPacket_gamma_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (zeroLedger' := zeroLedgerB) (gamma' := gammaB)
      (bundle := bundle) (pkg := pkg) packet gammaRouteB zeroLedgerSameB
  obtain ⟨gammaSameB, _namePkgB, _provenancePkgB⟩ := boundaryB
  have gammaAB : hsame gammaA gammaB :=
    hsame_trans (hsame_symm gammaSameA) gammaSameB
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed routesUnary nameUnary routesNameGamma
  exact
    ⟨gammaSameA, gammaSameB, gammaAB, gammaReadUnary, routesNameGamma, namePkg,
      provenancePkg, gammaPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
