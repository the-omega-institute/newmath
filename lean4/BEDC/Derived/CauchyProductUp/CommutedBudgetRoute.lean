import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_commuted_budget_route [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name commutedProduct commutedClassifier commutedSeal :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont observationB observationA commutedProduct ->
        hsame commutedProduct product ->
          Cont commutedProduct ledger commutedClassifier ->
            Cont commutedClassifier routes commutedSeal ->
              PkgSig bundle commutedSeal pkg ->
                UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory commutedProduct ∧
                  UnaryHistory commutedClassifier ∧ UnaryHistory commutedSeal ∧
                    hsame commutedProduct product ∧
                      Cont observationB observationA commutedProduct ∧
                        Cont commutedProduct ledger commutedClassifier ∧
                          Cont commutedClassifier routes commutedSeal ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle commutedSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont hsame
  intro packet commutedProductRoute sameProduct commutedClassifierRoute commutedSealRoute
    commutedSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have commutedProductUnary : UnaryHistory commutedProduct :=
    unary_cont_closed observationBUnary observationAUnary commutedProductRoute
  have commutedClassifierUnary : UnaryHistory commutedClassifier :=
    unary_cont_closed commutedProductUnary ledgerUnary commutedClassifierRoute
  have commutedSealUnary : UnaryHistory commutedSeal :=
    unary_cont_closed commutedClassifierUnary routesUnary commutedSealRoute
  exact
    ⟨windowAUnary, windowBUnary, commutedProductUnary, commutedClassifierUnary,
      commutedSealUnary, sameProduct, commutedProductRoute, commutedClassifierRoute,
      commutedSealRoute, namePkg, commutedSealPkg⟩

end BEDC.Derived.CauchyProductUp
