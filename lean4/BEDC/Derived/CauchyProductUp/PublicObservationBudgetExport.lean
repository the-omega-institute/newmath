import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_public_observation_budget_export [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal observationBudgetRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          UnaryHistory observationBudgetRead ->
            Cont budgetSeal observationBudgetRead publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory budgetClassifier ∧
                  UnaryHistory budgetSeal ∧ UnaryHistory observationBudgetRead ∧
                    UnaryHistory publicRead ∧ Cont observationA observationB product ∧
                      Cont product ledger classifier ∧
                        Cont classifier routes budgetClassifier ∧
                          Cont budgetClassifier ledger budgetSeal ∧
                            Cont budgetSeal observationBudgetRead publicRead ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute observationBudgetUnary publicRoute publicPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed budgetSealUnary observationBudgetUnary publicRoute
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      observationBudgetUnary, publicUnary, productRoute, classifierRoute, classifierBudget,
      budgetSealRoute, publicRoute, namePkg, publicPkg⟩

end BEDC.Derived.CauchyProductUp
