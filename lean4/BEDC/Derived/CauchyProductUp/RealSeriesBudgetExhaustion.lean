import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_series_budget_exhaustion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal seriesTail seriesEndpoint
      combinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          UnaryHistory seriesTail ->
            Cont budgetSeal seriesTail seriesEndpoint ->
              Cont seriesEndpoint routes combinedRead ->
                PkgSig bundle combinedRead pkg ->
                  UnaryHistory product ∧ UnaryHistory classifier ∧
                    UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                      UnaryHistory seriesEndpoint ∧ UnaryHistory combinedRead ∧
                        Cont observationA observationB product ∧ Cont product ledger classifier ∧
                          Cont classifier routes budgetClassifier ∧
                            Cont budgetClassifier ledger budgetSeal ∧
                              Cont budgetSeal seriesTail seriesEndpoint ∧
                                Cont seriesEndpoint routes combinedRead ∧
                                  PkgSig bundle name pkg ∧ PkgSig bundle combinedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute seriesTailUnary seriesEndpointRoute
    combinedReadRoute combinedReadPkg
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
  have seriesEndpointUnary : UnaryHistory seriesEndpoint :=
    unary_cont_closed budgetSealUnary seriesTailUnary seriesEndpointRoute
  have combinedReadUnary : UnaryHistory combinedRead :=
    unary_cont_closed seriesEndpointUnary routesUnary combinedReadRoute
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      seriesEndpointUnary, combinedReadUnary, productRoute, classifierRoute, classifierBudget,
      budgetSealRoute, seriesEndpointRoute, combinedReadRoute, namePkg, combinedReadPkg⟩

end BEDC.Derived.CauchyProductUp
