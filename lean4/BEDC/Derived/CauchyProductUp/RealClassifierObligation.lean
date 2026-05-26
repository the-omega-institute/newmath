import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_classifier_obligation [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      hsame classifierRead classifier ->
        UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory classifierRead ∧
          Cont observationA observationB product ∧ Cont product ledger classifier ∧
            hsame classifierRead classifier ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont PkgSig hsame UnaryHistory
  intro packet classifierReadSame
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_transport classifierUnary (hsame_symm classifierReadSame)
  exact
    ⟨productUnary, classifierUnary, classifierReadUnary, productRoute, classifierRoute,
      classifierReadSame, namePkg⟩

end BEDC.Derived.CauchyProductUp
