import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_series_handoff_exhaustion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name seriesTail seriesBudget seriesSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes seriesTail ->
        Cont seriesTail ledger seriesBudget ->
          Cont seriesBudget routes seriesSeal ->
            Cont seriesSeal ledger realSeal ->
              PkgSig bundle realSeal pkg ->
                UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory seriesTail ∧
                  UnaryHistory seriesBudget ∧ UnaryHistory seriesSeal ∧
                    UnaryHistory realSeal ∧ Cont product ledger classifier ∧
                      Cont classifier routes seriesTail ∧ Cont seriesTail ledger seriesBudget ∧
                        Cont seriesBudget routes seriesSeal ∧ Cont seriesSeal ledger realSeal ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierSeriesTail seriesTailBudget seriesBudgetSeal seriesSealRealSeal
    realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have seriesTailUnary : UnaryHistory seriesTail :=
    unary_cont_closed classifierUnary routesUnary classifierSeriesTail
  have seriesBudgetUnary : UnaryHistory seriesBudget :=
    unary_cont_closed seriesTailUnary ledgerUnary seriesTailBudget
  have seriesSealUnary : UnaryHistory seriesSeal :=
    unary_cont_closed seriesBudgetUnary routesUnary seriesBudgetSeal
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed seriesSealUnary ledgerUnary seriesSealRealSeal
  exact
    ⟨productUnary, classifierUnary, seriesTailUnary, seriesBudgetUnary, seriesSealUnary,
      realSealUnary, classifierRoute, classifierSeriesTail, seriesTailBudget,
      seriesBudgetSeal, seriesSealRealSeal, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
