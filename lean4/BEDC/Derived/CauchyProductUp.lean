import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyProductPacket [AskSetup] [PackageSetup]
    (sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
    UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
      UnaryHistory observationA ∧ UnaryHistory observationB ∧ UnaryHistory routes ∧
        UnaryHistory ledger ∧ Cont windowA windowB transport ∧
          Cont observationA observationB product ∧ Cont product ledger classifier ∧
            PkgSig bundle name pkg

theorem CauchyProductPacket_namecert_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
        UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
          UnaryHistory product ∧ UnaryHistory classifier ∧ Cont windowA windowB transport ∧
            Cont observationA observationB product ∧ Cont product ledger classifier ∧
              PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
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
      productUnary, classifierUnary, windowTransport, productRoute, classifierRoute, namePkg⟩

theorem CauchyProductPacket_root_regular_product_carrier_row [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
        UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
          UnaryHistory observationA ∧ UnaryHistory observationB ∧ UnaryHistory product ∧
            UnaryHistory classifier ∧ UnaryHistory routes ∧ UnaryHistory ledger ∧
              Cont windowA windowB transport ∧ Cont observationA observationB product ∧
                Cont product ledger classifier ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, productUnary, classifierUnary, routesUnary,
      ledgerUnary, windowTransport, productRoute, classifierRoute, namePkg⟩

theorem CauchyProductPacket_real_seal_boundary [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        PkgSig bundle realSeal pkg ->
          UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory realSeal ∧
            Cont product ledger classifier ∧ Cont classifier routes realSeal ∧
              PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet classifierRoutesRealSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRealSeal
  exact
    ⟨productUnary, classifierUnary, realSealUnary, classifierRoute, classifierRoutesRealSeal,
      namePkg, realSealPkg⟩

theorem CauchyProductPacket_window_product_stability [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory observationA ∧
        UnaryHistory observationB ∧ UnaryHistory product ∧
          Cont observationA observationB product ∧ Cont windowA windowB transport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, _ledgerUnary,
    windowTransport, productRoute, _classifierRoute, _namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  exact
    ⟨windowAUnary, windowBUnary, observationAUnary, observationBUnary, productUnary,
      productRoute, windowTransport⟩

theorem CauchyProductPacket_left_factor_classifier_congruence [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name replacementSource replacementWindow
      replacementProduct : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      hsame replacementSource sourceA ->
        Cont replacementSource windowA replacementWindow ->
          Cont replacementWindow windowB replacementProduct ->
            hsame replacementProduct product ->
              UnaryHistory replacementSource ∧ UnaryHistory replacementWindow ∧
                UnaryHistory replacementProduct ∧ hsame replacementProduct product ∧
                  Cont replacementWindow windowB replacementProduct ∧
                    Cont product ledger classifier ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet sameSource replacementWindowRoute replacementProductRoute sameProduct
  obtain ⟨sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, _productRoute, classifierRoute, namePkg⟩ := packet
  have replacementSourceUnary : UnaryHistory replacementSource :=
    unary_transport sourceAUnary (hsame_symm sameSource)
  have replacementWindowUnary : UnaryHistory replacementWindow :=
    unary_cont_closed replacementSourceUnary windowAUnary replacementWindowRoute
  have replacementProductUnary : UnaryHistory replacementProduct :=
    unary_cont_closed replacementWindowUnary windowBUnary replacementProductRoute
  exact
    ⟨replacementSourceUnary, replacementWindowUnary, replacementProductUnary, sameProduct,
      replacementProductRoute, classifierRoute, namePkg⟩

theorem CauchyProductPacket_root_budget_classifier_coverage [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont classifier routes budgetClassifier →
        Cont budgetClassifier ledger budgetSeal →
          PkgSig bundle budgetSeal pkg →
            UnaryHistory product ∧ UnaryHistory classifier ∧
              UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                Cont observationA observationB product ∧ Cont product ledger classifier ∧
                  Cont classifier routes budgetClassifier ∧
                    Cont budgetClassifier ledger budgetSeal ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet classifierBudget budgetSealRoute budgetSealPkg
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
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      productRoute, classifierRoute, classifierBudget, budgetSealRoute, namePkg,
      budgetSealPkg⟩

theorem CauchyProductPacket_root_source_diagonal_consistency [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont classifier routes budgetClassifier →
        Cont budgetClassifier ledger budgetSeal →
          Cont budgetSeal routes realSeal →
            PkgSig bundle realSeal pkg →
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
                  UnaryHistory observationA ∧ UnaryHistory observationB ∧
                    UnaryHistory product ∧ UnaryHistory classifier ∧
                      UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                        UnaryHistory realSeal ∧ Cont observationA observationB product ∧
                          Cont product ledger classifier ∧
                            Cont classifier routes budgetClassifier ∧
                              Cont budgetClassifier ledger budgetSeal ∧
                                Cont budgetSeal routes realSeal ∧ PkgSig bundle name pkg ∧
                                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet classifierBudget budgetSealRoute realSealRoute realSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
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
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, productUnary, classifierUnary,
      budgetClassifierUnary, budgetSealUnary, realSealUnary, productRoute, classifierRoute,
      classifierBudget, budgetSealRoute, realSealRoute, namePkg, realSealPkg⟩

theorem CauchyProductPacket_finite_window_real_seal_factorization [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
                  UnaryHistory observationA ∧ UnaryHistory observationB ∧
                    UnaryHistory product ∧ UnaryHistory classifier ∧
                      UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                        UnaryHistory realSeal ∧ Cont windowA windowB transport ∧
                          Cont observationA observationB product ∧
                            Cont product ledger classifier ∧
                              Cont classifier routes budgetClassifier ∧
                                Cont budgetClassifier ledger budgetSeal ∧
                                  Cont budgetSeal routes realSeal ∧
                                    PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute realSealRoute realSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
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
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, productUnary, classifierUnary,
      budgetClassifierUnary, budgetSealUnary, realSealUnary, windowTransport, productRoute,
      classifierRoute, classifierBudget, budgetSealRoute, realSealRoute, namePkg,
      realSealPkg⟩

theorem CauchyProductPacket_root_budget_nonescape [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          PkgSig bundle budgetSeal pkg ->
            UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
              UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
                UnaryHistory observationA ∧ UnaryHistory observationB ∧ UnaryHistory product ∧
                  UnaryHistory classifier ∧ UnaryHistory budgetClassifier ∧
                    UnaryHistory budgetSeal ∧ Cont windowA windowB transport ∧
                      Cont observationA observationB product ∧ Cont product ledger classifier ∧
                        Cont classifier routes budgetClassifier ∧
                          Cont budgetClassifier ledger budgetSeal ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute budgetSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, productUnary, classifierUnary, budgetClassifierUnary,
      budgetSealUnary, windowTransport, productRoute, classifierRoute, classifierBudget,
      budgetSealRoute, namePkg, budgetSealPkg⟩

theorem CauchyProductPacket_root_window_regseqrat_seal_route [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes regseqSeal ->
        PkgSig bundle regseqSeal pkg ->
          UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory observationA ∧
            UnaryHistory observationB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
              UnaryHistory regseqSeal ∧ Cont windowA windowB transport ∧
                Cont observationA observationB product ∧ Cont product ledger classifier ∧
                  Cont classifier routes regseqSeal ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle regseqSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRoutesSeal regseqSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesSeal
  exact
    ⟨windowAUnary, windowBUnary, observationAUnary, observationBUnary, productUnary,
      classifierUnary, regseqSealUnary, windowTransport, productRoute, classifierRoute,
      classifierRoutesSeal, namePkg, regseqSealPkg⟩

theorem CauchyProductPacket_root_regseq_seal_stability [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes regseqSeal ->
        Cont regseqSeal ledger realSeal ->
          PkgSig bundle realSeal pkg ->
            UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory regseqSeal ∧
              UnaryHistory realSeal ∧ Cont observationA observationB product ∧
                Cont product ledger classifier ∧ Cont classifier routes regseqSeal ∧
                  Cont regseqSeal ledger realSeal ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRoutesSeal regseqSealRealSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesSeal
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqSealUnary ledgerUnary regseqSealRealSeal
  exact
    ⟨productUnary, classifierUnary, regseqSealUnary, realSealUnary, productRoute,
      classifierRoute, classifierRoutesSeal, regseqSealRealSeal, namePkg, realSealPkg⟩

theorem CauchyProductPacket_budget_product_consumer_boundary [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory budgetClassifier ∧
                UnaryHistory budgetSeal ∧ UnaryHistory consumerRead ∧
                  Cont observationA observationB product ∧ Cont product ledger classifier ∧
                    Cont classifier routes budgetClassifier ∧
                      Cont budgetClassifier ledger budgetSeal ∧
                        Cont budgetSeal routes consumerRead ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute sealConsumerRead consumerReadPkg
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
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed budgetSealUnary routesUnary sealConsumerRead
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary, consumerReadUnary,
      productRoute, classifierRoute, classifierBudget, budgetSealRoute, sealConsumerRead, namePkg,
      consumerReadPkg⟩

theorem CauchyProductPacket_source_window_budget_compatibility [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name streamRead budgetClassifier budgetSeal
      compatibleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes streamRead ->
        Cont classifier routes budgetClassifier ->
          Cont budgetClassifier ledger budgetSeal ->
            Cont streamRead budgetSeal compatibleRead ->
              PkgSig bundle compatibleRead pkg ->
                UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                  UnaryHistory windowB ∧ UnaryHistory transport ∧ UnaryHistory streamRead ∧
                    UnaryHistory product ∧ UnaryHistory classifier ∧
                      UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                        UnaryHistory compatibleRead ∧ Cont windowA windowB transport ∧
                          Cont transport routes streamRead ∧
                            Cont observationA observationB product ∧
                              Cont product ledger classifier ∧
                                Cont classifier routes budgetClassifier ∧
                                  Cont budgetClassifier ledger budgetSeal ∧
                                    Cont streamRead budgetSeal compatibleRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle compatibleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportRoutesStreamRead classifierBudget budgetSealRoute compatibleRoute
    compatiblePkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed transportUnary routesUnary transportRoutesStreamRead
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have compatibleReadUnary : UnaryHistory compatibleRead :=
    unary_cont_closed streamReadUnary budgetSealUnary compatibleRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, transportUnary,
      streamReadUnary, productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      compatibleReadUnary, windowTransport, transportRoutesStreamRead, productRoute,
      classifierRoute, classifierBudget, budgetSealRoute, compatibleRoute, namePkg,
      compatiblePkg⟩

theorem CauchyProductPacket_realalgorder_completion_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal realAlgOrderConsumer
      completionConsumer realAlgOrderRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          UnaryHistory realAlgOrderConsumer ->
            UnaryHistory completionConsumer ->
              Cont budgetSeal realAlgOrderConsumer realAlgOrderRead ->
                Cont budgetSeal completionConsumer completionRead ->
                  PkgSig bundle realAlgOrderRead pkg ->
                    PkgSig bundle completionRead pkg ->
                      UnaryHistory product ∧ UnaryHistory classifier ∧
                        UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                          UnaryHistory realAlgOrderRead ∧ UnaryHistory completionRead ∧
                            Cont product ledger classifier ∧
                              Cont classifier routes budgetClassifier ∧
                                Cont budgetClassifier ledger budgetSeal ∧
                                  Cont budgetSeal realAlgOrderConsumer realAlgOrderRead ∧
                                    Cont budgetSeal completionConsumer completionRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle realAlgOrderRead pkg ∧
                                          PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute realAlgOrderConsumerUnary
    completionConsumerUnary realAlgOrderRoute completionRoute realAlgOrderPkg completionPkg
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
  have realAlgOrderReadUnary : UnaryHistory realAlgOrderRead :=
    unary_cont_closed budgetSealUnary realAlgOrderConsumerUnary realAlgOrderRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetSealUnary completionConsumerUnary completionRoute
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary,
      realAlgOrderReadUnary, completionReadUnary, classifierRoute, classifierBudget,
      budgetSealRoute, realAlgOrderRoute, completionRoute, namePkg, realAlgOrderPkg,
      completionPkg⟩

theorem CauchyProductPacket_budget_triangle_selector_compatibility [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal selectorRead
      finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
      Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes selectorRead ->
            Cont selectorRead ledger finalRead ->
              PkgSig bundle finalRead pkg ->
                UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory budgetClassifier ∧ UnaryHistory budgetSeal ∧
                    UnaryHistory selectorRead ∧ UnaryHistory finalRead ∧
                      Cont observationA observationB product ∧
                        Cont product ledger classifier ∧
                          Cont classifier routes budgetClassifier ∧
                            Cont budgetClassifier ledger budgetSeal ∧
                              Cont budgetSeal routes selectorRead ∧
                                Cont selectorRead ledger finalRead ∧ PkgSig bundle name pkg ∧
                                  PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute sealSelectorRead selectorFinalRead finalReadPkg
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
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed budgetSealUnary routesUnary sealSelectorRead
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed selectorReadUnary ledgerUnary selectorFinalRead
  exact
    ⟨productUnary, classifierUnary, budgetClassifierUnary, budgetSealUnary, selectorReadUnary,
      finalReadUnary, productRoute, classifierRoute, classifierBudget, budgetSealRoute,
      sealSelectorRead, selectorFinalRead, namePkg, finalReadPkg⟩

theorem CauchyProductPacket_real_seal_source_budget_nonescape [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes realSeal ->
        PkgSig bundle realSeal pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
              UnaryHistory observationA ∧ UnaryHistory observationB ∧
                UnaryHistory transport ∧ UnaryHistory realSeal ∧
                  Cont windowA windowB transport ∧ Cont transport routes realSeal ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportRoutesRealSeal realSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, _ledgerUnary,
    windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed transportUnary routesUnary transportRoutesRealSeal
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, transportUnary, realSealUnary, windowTransport,
      transportRoutesRealSeal, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
