import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_shared_selector_regseqrat_real_seal_commutation
    [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name selectorWindow selectorDyadic selectorBudget
      regSeqSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory selectorWindow ->
        UnaryHistory selectorDyadic ->
          Cont selectorWindow selectorDyadic selectorBudget ->
            Cont product selectorBudget regSeqSeal ->
              Cont classifier selectorBudget realSeal ->
                PkgSig bundle regSeqSeal pkg ->
                  PkgSig bundle realSeal pkg ->
                    UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory selectorBudget ∧
                      UnaryHistory regSeqSeal ∧ UnaryHistory realSeal ∧
                        Cont selectorWindow selectorDyadic selectorBudget ∧
                          Cont product selectorBudget regSeqSeal ∧
                            Cont classifier selectorBudget realSeal ∧
                              PkgSig bundle regSeqSeal pkg ∧
                                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet selectorWindowUnary selectorDyadicUnary selectorBudgetRoute regSeqSealRoute
    realSealRoute regSeqSealPkg realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, _namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have selectorBudgetUnary : UnaryHistory selectorBudget :=
    unary_cont_closed selectorWindowUnary selectorDyadicUnary selectorBudgetRoute
  have regSeqSealUnary : UnaryHistory regSeqSeal :=
    unary_cont_closed productUnary selectorBudgetUnary regSeqSealRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary selectorBudgetUnary realSealRoute
  exact
    ⟨productUnary, classifierUnary, selectorBudgetUnary, regSeqSealUnary, realSealUnary,
      selectorBudgetRoute, regSeqSealRoute, realSealRoute, regSeqSealPkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
