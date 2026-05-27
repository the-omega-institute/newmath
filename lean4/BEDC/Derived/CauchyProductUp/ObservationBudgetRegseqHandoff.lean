import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_observation_budget_regseq_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetWindow budgetDyadic budgetRegSeq : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetWindow ->
        Cont budgetWindow ledger budgetDyadic ->
          Cont budgetDyadic routes budgetRegSeq ->
            PkgSig bundle budgetRegSeq pkg ->
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory budgetWindow ∧
                UnaryHistory budgetDyadic ∧ UnaryHistory budgetRegSeq ∧
                  Cont product ledger classifier ∧ Cont classifier routes budgetWindow ∧
                    Cont budgetWindow ledger budgetDyadic ∧
                      Cont budgetDyadic routes budgetRegSeq ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle budgetRegSeq pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet classifierBudget budgetDyadicRoute budgetRegSeqRoute budgetRegSeqPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetDyadicUnary : UnaryHistory budgetDyadic :=
    unary_cont_closed budgetWindowUnary ledgerUnary budgetDyadicRoute
  have budgetRegSeqUnary : UnaryHistory budgetRegSeq :=
    unary_cont_closed budgetDyadicUnary routesUnary budgetRegSeqRoute
  exact
    ⟨productUnary, classifierUnary, budgetWindowUnary, budgetDyadicUnary,
      budgetRegSeqUnary, classifierRoute, classifierBudget, budgetDyadicRoute,
      budgetRegSeqRoute, namePkg, budgetRegSeqPkg⟩

end BEDC.Derived.CauchyProductUp
