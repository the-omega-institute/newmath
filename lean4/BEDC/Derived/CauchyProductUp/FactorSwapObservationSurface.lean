import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_factor_swap_observation_surface [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name swappedProduct swappedClassifier realSeal :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont observationB observationA swappedProduct ->
        Cont swappedProduct ledger swappedClassifier ->
          Cont swappedClassifier routes realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory observationA ∧
                UnaryHistory observationB ∧ UnaryHistory swappedProduct ∧
                  UnaryHistory swappedClassifier ∧ UnaryHistory realSeal ∧
                    Cont observationB observationA swappedProduct ∧
                      Cont swappedProduct ledger swappedClassifier ∧
                        Cont swappedClassifier routes realSeal ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet swappedProductRoute swappedClassifierRoute realSealRoute realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have swappedProductUnary : UnaryHistory swappedProduct :=
    unary_cont_closed observationBUnary observationAUnary swappedProductRoute
  have swappedClassifierUnary : UnaryHistory swappedClassifier :=
    unary_cont_closed swappedProductUnary ledgerUnary swappedClassifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed swappedClassifierUnary routesUnary realSealRoute
  exact
    ⟨windowAUnary, windowBUnary, observationAUnary, observationBUnary, swappedProductUnary,
      swappedClassifierUnary, realSealUnary, swappedProductRoute, swappedClassifierRoute,
      realSealRoute, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
