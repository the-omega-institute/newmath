import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_two_factor_classifier_descent [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name replacementSourceA replacementSourceB
      replacementWindowA replacementWindowB replacementProduct : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      hsame replacementSourceA sourceA ->
        hsame replacementSourceB sourceB ->
          Cont replacementSourceA windowA replacementWindowA ->
            Cont replacementSourceB windowB replacementWindowB ->
              Cont replacementWindowA replacementWindowB replacementProduct ->
                hsame replacementProduct product ->
                  UnaryHistory replacementSourceA ∧ UnaryHistory replacementSourceB ∧
                    UnaryHistory replacementWindowA ∧ UnaryHistory replacementWindowB ∧
                      UnaryHistory replacementProduct ∧ hsame replacementProduct product ∧
                        Cont replacementWindowA replacementWindowB replacementProduct ∧
                          Cont product ledger classifier ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg hsame Cont
  intro packet sameSourceA sameSourceB replacementWindowARoute replacementWindowBRoute
    replacementProductRoute sameProduct
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, _productRoute, classifierRoute, namePkg⟩ := packet
  have replacementSourceAUnary : UnaryHistory replacementSourceA :=
    unary_transport sourceAUnary (hsame_symm sameSourceA)
  have replacementSourceBUnary : UnaryHistory replacementSourceB :=
    unary_transport sourceBUnary (hsame_symm sameSourceB)
  have replacementWindowAUnary : UnaryHistory replacementWindowA :=
    unary_cont_closed replacementSourceAUnary windowAUnary replacementWindowARoute
  have replacementWindowBUnary : UnaryHistory replacementWindowB :=
    unary_cont_closed replacementSourceBUnary windowBUnary replacementWindowBRoute
  have replacementProductUnary : UnaryHistory replacementProduct :=
    unary_cont_closed replacementWindowAUnary replacementWindowBUnary replacementProductRoute
  exact
    ⟨replacementSourceAUnary, replacementSourceBUnary, replacementWindowAUnary,
      replacementWindowBUnary, replacementProductUnary, sameProduct, replacementProductRoute,
      classifierRoute, namePkg⟩

end BEDC.Derived.CauchyProductUp
