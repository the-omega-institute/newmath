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
      classifier transport routes ledger name swappedTransport swappedProduct commutedClassifier
      regseqSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont windowB windowA swappedTransport ->
        Cont observationB observationA swappedProduct ->
          Cont swappedProduct ledger commutedClassifier ->
            Cont commutedClassifier routes regseqSeal ->
              Cont regseqSeal ledger realSeal ->
                PkgSig bundle realSeal pkg ->
                  UnaryHistory windowA ∧ UnaryHistory windowB ∧
                    UnaryHistory swappedTransport ∧ UnaryHistory swappedProduct ∧
                      UnaryHistory commutedClassifier ∧ UnaryHistory regseqSeal ∧
                        UnaryHistory realSeal ∧ Cont windowB windowA swappedTransport ∧
                          Cont observationB observationA swappedProduct ∧
                            Cont swappedProduct ledger commutedClassifier ∧
                              Cont commutedClassifier routes regseqSeal ∧
                                Cont regseqSeal ledger realSeal ∧ PkgSig bundle name pkg ∧
                                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet swappedTransportRoute swappedProductRoute commutedClassifierRoute regseqRoute
    realSealRoute realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have swappedTransportUnary : UnaryHistory swappedTransport :=
    unary_cont_closed windowBUnary windowAUnary swappedTransportRoute
  have swappedProductUnary : UnaryHistory swappedProduct :=
    unary_cont_closed observationBUnary observationAUnary swappedProductRoute
  have commutedClassifierUnary : UnaryHistory commutedClassifier :=
    unary_cont_closed swappedProductUnary ledgerUnary commutedClassifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed commutedClassifierUnary routesUnary regseqRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqSealUnary ledgerUnary realSealRoute
  exact
    ⟨windowAUnary, windowBUnary, swappedTransportUnary, swappedProductUnary,
      commutedClassifierUnary, regseqSealUnary, realSealUnary, swappedTransportRoute,
      swappedProductRoute, commutedClassifierRoute, regseqRoute, realSealRoute, namePkg,
      realSealPkg⟩

end BEDC.Derived.CauchyProductUp
