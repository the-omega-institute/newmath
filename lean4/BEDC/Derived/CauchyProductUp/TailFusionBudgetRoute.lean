import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_tail_fusion_budget_route [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name tailFusion tailBudget realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes tailFusion ->
        Cont tailFusion ledger tailBudget ->
          Cont tailBudget transport realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory tailFusion ∧
                UnaryHistory tailBudget ∧ UnaryHistory realSeal ∧ Cont product ledger classifier ∧
                  Cont classifier routes tailFusion ∧ Cont tailFusion ledger tailBudget ∧
                    Cont tailBudget transport realSeal ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet classifierTailFusion tailFusionBudget tailBudgetRealSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have tailFusionUnary : UnaryHistory tailFusion :=
    unary_cont_closed classifierUnary routesUnary classifierTailFusion
  have tailBudgetUnary : UnaryHistory tailBudget :=
    unary_cont_closed tailFusionUnary ledgerUnary tailFusionBudget
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed tailBudgetUnary transportUnary tailBudgetRealSeal
  exact
    ⟨productUnary, classifierUnary, tailFusionUnary, tailBudgetUnary, realSealUnary,
      classifierRoute, classifierTailFusion, tailFusionBudget, tailBudgetRealSeal, namePkg,
      realSealPkg⟩

end BEDC.Derived.CauchyProductUp
