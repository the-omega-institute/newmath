import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_shared_selector_budget_totality [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal productSeal seriesTail
      seriesWindow seriesReadback seriesSeal terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory seriesTail ->
        UnaryHistory seriesWindow ->
          Cont classifier routes budgetClassifier ->
            Cont budgetClassifier ledger budgetSeal ->
              Cont budgetSeal routes productSeal ->
                Cont seriesTail seriesWindow seriesReadback ->
                  Cont seriesReadback budgetSeal seriesSeal ->
                    Cont productSeal seriesSeal terminal ->
                      PkgSig bundle terminal pkg ->
                        UnaryHistory product ∧ UnaryHistory classifier ∧
                          UnaryHistory budgetSeal ∧ UnaryHistory productSeal ∧
                            UnaryHistory seriesReadback ∧ UnaryHistory seriesSeal ∧
                              UnaryHistory terminal ∧ Cont product ledger classifier ∧
                                Cont classifier routes budgetClassifier ∧
                                  Cont budgetClassifier ledger budgetSeal ∧
                                    Cont budgetSeal routes productSeal ∧
                                      Cont seriesTail seriesWindow seriesReadback ∧
                                        Cont seriesReadback budgetSeal seriesSeal ∧
                                          Cont productSeal seriesSeal terminal ∧
                                            PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet seriesTailUnary seriesWindowUnary classifierBudget budgetSealRoute productSealRoute
    seriesReadbackRoute seriesSealRoute terminalRoute terminalPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, _namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed budgetSealUnary routesUnary productSealRoute
  have seriesReadbackUnary : UnaryHistory seriesReadback :=
    unary_cont_closed seriesTailUnary seriesWindowUnary seriesReadbackRoute
  have seriesSealUnary : UnaryHistory seriesSeal :=
    unary_cont_closed seriesReadbackUnary budgetSealUnary seriesSealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed productSealUnary seriesSealUnary terminalRoute
  exact
    ⟨productUnary, classifierUnary, budgetSealUnary, productSealUnary, seriesReadbackUnary,
      seriesSealUnary, terminalUnary, classifierRoute, classifierBudget, budgetSealRoute,
      productSealRoute, seriesReadbackRoute, seriesSealRoute, terminalRoute, terminalPkg⟩

end BEDC.Derived.CauchyProductUp
