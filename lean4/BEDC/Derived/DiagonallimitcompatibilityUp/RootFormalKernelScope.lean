import BEDC.Derived.DiagonallimitcompatibilityUp.RootFormalSource

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootFormalKernelScope [AskSetup] [PackageSetup]
    {budget selector window regseq realSeal transport route provenance cert rootBudget
      rootWindow rootReadback rootSeal support : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityRootFormalSource budget selector window regseq realSeal transport
        route provenance cert bundle pkg →
      Cont budget selector rootBudget →
        Cont rootBudget window rootWindow →
          Cont rootWindow regseq rootReadback →
            Cont rootReadback realSeal rootSeal →
              Cont route cert support →
                PkgSig bundle support pkg →
                  UnaryHistory budget ∧ UnaryHistory selector ∧ UnaryHistory window ∧
                    UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory route ∧
                      UnaryHistory cert ∧ UnaryHistory rootBudget ∧
                        UnaryHistory rootWindow ∧ UnaryHistory rootReadback ∧
                          UnaryHistory rootSeal ∧ UnaryHistory support ∧
                            Cont budget selector rootBudget ∧
                              Cont rootBudget window rootWindow ∧
                                Cont rootWindow regseq rootReadback ∧
                                  Cont rootReadback realSeal rootSeal ∧
                                    Cont route cert support ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle support pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro source budgetSelectorRoot rootBudgetWindowRoot rootWindowRegseqReadback
    rootReadbackRealSealRoot routeCertSupport supportPkg
  obtain ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary,
    _transportUnary, routeUnary, _provenanceUnary, certUnary, _budgetSelectorWindow,
    _windowRegseqRealSeal, _transportRouteCert, provenancePkg⟩ := source
  have rootBudgetUnary : UnaryHistory rootBudget :=
    unary_cont_closed budgetUnary selectorUnary budgetSelectorRoot
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed rootBudgetUnary windowUnary rootBudgetWindowRoot
  have rootReadbackUnary : UnaryHistory rootReadback :=
    unary_cont_closed rootWindowUnary regseqUnary rootWindowRegseqReadback
  have rootSealUnary : UnaryHistory rootSeal :=
    unary_cont_closed rootReadbackUnary realSealUnary rootReadbackRealSealRoot
  have supportUnary : UnaryHistory support :=
    unary_cont_closed routeUnary certUnary routeCertSupport
  exact
    ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary, routeUnary,
      certUnary, rootBudgetUnary, rootWindowUnary, rootReadbackUnary, rootSealUnary,
      supportUnary, budgetSelectorRoot, rootBudgetWindowRoot, rootWindowRegseqReadback,
      rootReadbackRealSealRoot, routeCertSupport, provenancePkg, supportPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
