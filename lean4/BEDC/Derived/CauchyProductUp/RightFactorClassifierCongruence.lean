import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_right_factor_classifier_congruence [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name replacementSource replacementWindow
      replacementProduct : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      hsame replacementSource sourceB ->
        Cont replacementSource windowB replacementWindow ->
          Cont windowA replacementWindow replacementProduct ->
            hsame replacementProduct product ->
              UnaryHistory replacementSource ∧ UnaryHistory replacementWindow ∧
                UnaryHistory replacementProduct ∧ hsame replacementProduct product ∧
                  Cont windowA replacementWindow replacementProduct ∧
                    Cont product ledger classifier ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet sameSource replacementWindowRoute replacementProductRoute sameProduct
  obtain ⟨_sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, _productRoute, classifierRoute, namePkg⟩ := packet
  have replacementSourceUnary : UnaryHistory replacementSource :=
    unary_transport sourceBUnary (hsame_symm sameSource)
  have replacementWindowUnary : UnaryHistory replacementWindow :=
    unary_cont_closed replacementSourceUnary windowBUnary replacementWindowRoute
  have replacementProductUnary : UnaryHistory replacementProduct :=
    unary_cont_closed windowAUnary replacementWindowUnary replacementProductRoute
  exact
    ⟨replacementSourceUnary, replacementWindowUnary, replacementProductUnary, sameProduct,
      replacementProductRoute, classifierRoute, namePkg⟩

end BEDC.Derived.CauchyProductUp
