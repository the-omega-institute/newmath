import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_source_window_admission [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
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
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRoutesSeal regseqSealRealSeal realSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesSeal
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqSealUnary ledgerUnary regseqSealRealSeal
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary,
      classifierUnary, regseqSealUnary, realSealUnary, windowTransport, productRoute,
      classifierRoute, classifierRoutesSeal, regseqSealRealSeal, namePkg, realSealPkg⟩

theorem CauchyProductPacket_real_budget_multiplication_boundary [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal selectorRead
      multiplicationSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes selectorRead ->
            Cont selectorRead ledger multiplicationSeal ->
              PkgSig bundle multiplicationSeal pkg ->
                UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
                  UnaryHistory classifier ∧ UnaryHistory budgetClassifier ∧
                    UnaryHistory budgetSeal ∧ UnaryHistory selectorRead ∧
                      UnaryHistory multiplicationSeal ∧ Cont observationA observationB product ∧
                        Cont product ledger classifier ∧
                          Cont classifier routes budgetClassifier ∧
                            Cont budgetClassifier ledger budgetSeal ∧
                              Cont budgetSeal routes selectorRead ∧
                                Cont selectorRead ledger multiplicationSeal ∧
                                  PkgSig bundle name pkg ∧
                                    PkgSig bundle multiplicationSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute sealSelectorRead selectorMultiplication
    multiplicationSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
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
  have multiplicationSealUnary : UnaryHistory multiplicationSeal :=
    unary_cont_closed selectorReadUnary ledgerUnary selectorMultiplication
  exact
    ⟨windowAUnary, windowBUnary, productUnary, classifierUnary, budgetClassifierUnary,
      budgetSealUnary, selectorReadUnary, multiplicationSealUnary, productRoute,
      classifierRoute, classifierBudget, budgetSealRoute, sealSelectorRead,
      selectorMultiplication, namePkg, multiplicationSealPkg⟩

theorem CauchyProductPacket_root_source_window_strict_obstruction [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes realSeal ->
        Cont realSeal ledger obstructionRead ->
          PkgSig bundle obstructionRead pkg ->
            UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
              UnaryHistory windowB ∧ UnaryHistory transport ∧ UnaryHistory realSeal ∧
                UnaryHistory obstructionRead ∧ Cont windowA windowB transport ∧
                  Cont transport routes realSeal ∧ Cont realSeal ledger obstructionRead ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportRoutesRealSeal realSealLedgerObstruction obstructionPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, routesUnary, ledgerUnary,
    windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed transportUnary routesUnary transportRoutesRealSeal
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed realSealUnary ledgerUnary realSealLedgerObstruction
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, transportUnary,
      realSealUnary, obstructionUnary, windowTransport, transportRoutesRealSeal,
      realSealLedgerObstruction, namePkg, obstructionPkg⟩

end BEDC.Derived.CauchyProductUp
