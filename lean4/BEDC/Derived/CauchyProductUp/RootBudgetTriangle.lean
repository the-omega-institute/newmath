import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_budget_triangle_real_seal_exhaustion [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal budgetRead
      finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal transport realSeal ->
            Cont realSeal routes budgetRead ->
              Cont budgetRead ledger finalRead ->
                PkgSig bundle finalRead pkg ->
                  UnaryHistory product ∧ UnaryHistory classifier ∧
                    UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                      UnaryHistory realSeal ∧ UnaryHistory budgetRead ∧
                        UnaryHistory finalRead ∧ Cont product ledger classifier ∧
                          Cont classifier routes budgetClassifier ∧
                            Cont budgetClassifier ledger budgetSeal ∧
                              Cont budgetSeal transport realSeal ∧
                                Cont realSeal routes budgetRead ∧
                                  Cont budgetRead ledger finalRead ∧
                                    PkgSig bundle name pkg ∧
                                      PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute sealTransportRead sealBudgetRead
    budgetFinalRead finalReadPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetSealUnary transportUnary sealTransportRead
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed realSealUnary routesUnary sealBudgetRead
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed budgetReadUnary ledgerUnary budgetFinalRead
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary, realSealUnary,
      budgetReadUnary, finalReadUnary, classifierRoute, classifierBudget, budgetSealRoute,
      sealTransportRead, sealBudgetRead, budgetFinalRead, namePkg, finalReadPkg⟩

theorem CauchyProductPacket_observation_budget_downstream_coverage [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal downstreamRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realSeal ->
            Cont realSeal ledger downstreamRead ->
              Cont downstreamRead routes completionRead ->
                PkgSig bundle completionRead pkg ->
                  UnaryHistory product ∧ UnaryHistory classifier ∧
                    UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                      UnaryHistory realSeal ∧ UnaryHistory downstreamRead ∧
                        UnaryHistory completionRead ∧ Cont observationA observationB product ∧
                          Cont product ledger classifier ∧
                            Cont classifier routes budgetClassifier ∧
                              Cont budgetClassifier ledger budgetSeal ∧
                                Cont budgetSeal routes realSeal ∧
                                  Cont realSeal ledger downstreamRead ∧
                                    Cont downstreamRead routes completionRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute realSealRoute downstreamReadRoute
    completionReadRoute completionReadPkg
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
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed budgetSealUnary routesUnary realSealRoute
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed realSealUnary ledgerUnary downstreamReadRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed downstreamReadUnary routesUnary completionReadRoute
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      realSealUnary, downstreamReadUnary, completionReadUnary, productRoute, classifierRoute,
      classifierBudget, budgetSealRoute, realSealRoute, downstreamReadRoute,
      completionReadRoute, namePkg, completionReadPkg⟩

end BEDC.Derived.CauchyProductUp
