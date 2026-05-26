import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_budget_fusion_nonescape [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name tailFusion tailBudget realSeal finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes tailFusion ->
        Cont tailFusion ledger tailBudget ->
          Cont tailBudget transport realSeal ->
            Cont realSeal routes finalRead ->
              PkgSig bundle finalRead pkg ->
                UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory tailFusion ∧
                  UnaryHistory tailBudget ∧ UnaryHistory realSeal ∧ UnaryHistory finalRead ∧
                    Cont observationA observationB product ∧ Cont product ledger classifier ∧
                      Cont classifier routes tailFusion ∧ Cont tailFusion ledger tailBudget ∧
                        Cont tailBudget transport realSeal ∧ Cont realSeal routes finalRead ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierTailFusion tailFusionBudget tailBudgetReal realFinal finalPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have tailFusionUnary : UnaryHistory tailFusion :=
    unary_cont_closed classifierUnary routesUnary classifierTailFusion
  have tailBudgetUnary : UnaryHistory tailBudget :=
    unary_cont_closed tailFusionUnary ledgerUnary tailFusionBudget
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed tailBudgetUnary transportUnary tailBudgetReal
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed realSealUnary routesUnary realFinal
  exact
    ⟨productUnary, classifierUnary, tailFusionUnary, tailBudgetUnary, realSealUnary,
      finalReadUnary, productRoute, classifierRoute, classifierTailFusion, tailFusionBudget,
      tailBudgetReal, realFinal, namePkg, finalPkg⟩

end BEDC.Derived.CauchyProductUp
