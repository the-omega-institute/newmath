import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_shared_window_root_admission [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name streamRead regseqSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes streamRead ->
        Cont classifier routes regseqSeal ->
          Cont regseqSeal ledger realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory regseqSeal ∧ UnaryHistory realSeal ∧
                    Cont windowA windowB transport ∧ Cont observationA observationB product ∧
                      Cont product ledger classifier ∧ Cont classifier routes regseqSeal ∧
                        Cont regseqSeal ledger realSeal ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet _transportRoutesStreamRead classifierRoutesRegseq regseqLedgerReal realSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRegseq
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqSealUnary ledgerUnary regseqLedgerReal
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary,
      classifierUnary, regseqSealUnary, realSealUnary, windowTransport, productRoute,
      classifierRoute, classifierRoutesRegseq, regseqLedgerReal, namePkg, realSealPkg⟩

theorem CauchyProductPacket_budgeted_root_source_triple [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
        UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
          UnaryHistory observationA ∧ UnaryHistory observationB ∧ UnaryHistory product ∧
            UnaryHistory classifier ∧ Cont windowA windowB transport ∧
              Cont observationA observationB product ∧ Cont product ledger classifier ∧
                PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, productUnary, classifierUnary, windowTransport,
      productRoute, classifierRoute, namePkg⟩

theorem CauchyProductPacket_real_completion_consumer_lock [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                    UnaryHistory consumerRead ∧ Cont windowA windowB transport ∧
                      Cont observationA observationB product ∧ Cont product ledger classifier ∧
                        Cont classifier routes budgetClassifier ∧
                          Cont budgetClassifier ledger budgetSeal ∧
                            Cont budgetSeal routes consumerRead ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute sealConsumerRead consumerReadPkg
  obtain ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
    consumerReadUnary, productRoute, classifierRoute, classifierBudgetRoute,
    budgetSealRoute', sealConsumerReadRoute, namePkg, consumerReadPkg'⟩ :=
    CauchyProductPacket_budget_product_consumer_boundary packet classifierBudget budgetSealRoute
      sealConsumerRead consumerReadPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, _routesUnary, _ledgerUnary,
    windowTransport, _productRoute, _classifierRoute, _namePkg⟩ := packet
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary, classifierUnary,
      budgetClassifierUnary, budgetSealUnary, consumerReadUnary, windowTransport, productRoute,
      classifierRoute, classifierBudgetRoute, budgetSealRoute', sealConsumerReadRoute, namePkg,
      consumerReadPkg'⟩

end BEDC.Derived.CauchyProductUp
