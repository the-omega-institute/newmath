import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_unblock_certificate [AskSetup] [PackageSetup]
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
                UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory budgetSeal ∧ UnaryHistory realSeal ∧
                    Cont windowA windowB transport ∧ Cont observationA observationB product ∧
                      Cont product ledger classifier ∧ Cont classifier routes budgetClassifier ∧
                        Cont budgetClassifier ledger budgetSeal ∧
                          Cont budgetSeal routes realSeal ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetSealRoute realSealRoute realSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
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
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary,
      classifierUnary, budgetSealUnary, realSealUnary, windowTransport, productRoute,
      classifierRoute, classifierBudget, budgetSealRoute, realSealRoute, namePkg,
      realSealPkg⟩

theorem CauchyProductPacket_root_phase_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name streamRead regseqSeal realSeal phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes streamRead ->
        Cont classifier routes regseqSeal ->
          Cont regseqSeal ledger realSeal ->
            Cont streamRead realSeal phaseRead ->
              PkgSig bundle phaseRead pkg ->
                UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory transport ∧
                  UnaryHistory streamRead ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                    UnaryHistory regseqSeal ∧ UnaryHistory realSeal ∧ UnaryHistory phaseRead ∧
                      Cont windowA windowB transport ∧ Cont transport routes streamRead ∧
                        Cont observationA observationB product ∧
                          Cont product ledger classifier ∧ Cont classifier routes regseqSeal ∧
                            Cont regseqSeal ledger realSeal ∧
                              Cont streamRead realSeal phaseRead ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle phaseRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet transportRoutes classifierRoutes regseqLedger streamReal phaseReadPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed transportUnary routesUnary transportRoutes
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutes
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqSealUnary ledgerUnary regseqLedger
  have phaseReadUnary : UnaryHistory phaseRead :=
    unary_cont_closed streamReadUnary realSealUnary streamReal
  exact
    ⟨windowAUnary, windowBUnary, transportUnary, streamReadUnary, productUnary,
      classifierUnary, regseqSealUnary, realSealUnary, phaseReadUnary, windowTransport,
      transportRoutes, productRoute, classifierRoute, classifierRoutes, regseqLedger,
      streamReal, namePkg, phaseReadPkg⟩

end BEDC.Derived.CauchyProductUp
