import BEDC.Derived.ModulusContinuityUp.TasteGate

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ModulusContinuityWindowMonotonicity [AskSetup] [PackageSetup]
    {graph sourceWindow modulus dyadic readback realSeal refinedBudget toleranceRead firstWindow
      refinedWindow graphRead readbackRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory graph →
      UnaryHistory sourceWindow →
        UnaryHistory modulus →
          UnaryHistory dyadic →
            UnaryHistory readback →
              UnaryHistory realSeal →
                UnaryHistory refinedBudget →
                  Cont dyadic modulus toleranceRead →
                    Cont toleranceRead sourceWindow firstWindow →
                      Cont firstWindow refinedBudget refinedWindow →
                        Cont refinedWindow graph graphRead →
                          Cont graphRead readback readbackRead →
                            Cont readbackRead realSeal realRead →
                              PkgSig bundle realRead pkg →
                                UnaryHistory toleranceRead ∧ UnaryHistory firstWindow ∧
                                  UnaryHistory refinedWindow ∧ UnaryHistory graphRead ∧
                                    UnaryHistory readbackRead ∧ UnaryHistory realRead ∧
                                      hsame refinedWindow (append firstWindow refinedBudget) ∧
                                        PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame append UnaryHistory
  intro graphUnary sourceWindowUnary modulusUnary dyadicUnary readbackUnary realSealUnary
    refinedBudgetUnary toleranceRoute firstWindowRoute refinedWindowRoute graphRoute
    readbackRoute realRoute realPkg
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed dyadicUnary modulusUnary toleranceRoute
  have firstWindowUnary : UnaryHistory firstWindow :=
    unary_cont_closed toleranceUnary sourceWindowUnary firstWindowRoute
  have refinedWindowUnary : UnaryHistory refinedWindow :=
    unary_cont_closed firstWindowUnary refinedBudgetUnary refinedWindowRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed refinedWindowUnary graphUnary graphRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed graphReadUnary readbackUnary readbackRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackReadUnary realSealUnary realRoute
  have refinedExact : hsame refinedWindow (append firstWindow refinedBudget) :=
    refinedWindowRoute
  exact
    ⟨toleranceUnary, firstWindowUnary, refinedWindowUnary, graphReadUnary, readbackReadUnary,
      realReadUnary, refinedExact, realPkg⟩

end BEDC.Derived.ModulusContinuityUp
