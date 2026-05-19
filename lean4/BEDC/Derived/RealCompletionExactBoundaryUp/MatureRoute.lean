import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryMatureRoute [AskSetup] [PackageSetup]
    {L K J S W R D E H C P N sealRead classifierRead witnessRead budgetRead terminalRead
      matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory K ->
        UnaryHistory J ->
          UnaryHistory S ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory E ->
                  UnaryHistory H ->
                    Cont L K sealRead ->
                      Cont sealRead J classifierRead ->
                        Cont classifierRead S witnessRead ->
                          Cont W R budgetRead ->
                            Cont budgetRead E terminalRead ->
                              Cont terminalRead H matureRead ->
                                PkgSig bundle matureRead pkg ->
                                  realCompletionExactBoundaryFields
                                      (RealCompletionExactBoundaryUp.mk L K J S W R D E H C P N) =
                                    [L, K, J, S, W, R, D, E, H, C, P, N] ∧
                                    UnaryHistory sealRead ∧
                                      UnaryHistory classifierRead ∧
                                        UnaryHistory witnessRead ∧
                                          UnaryHistory budgetRead ∧
                                            UnaryHistory terminalRead ∧
                                              UnaryHistory matureRead ∧
                                                Cont L K sealRead ∧
                                                  Cont sealRead J classifierRead ∧
                                                    Cont classifierRead S witnessRead ∧
                                                      Cont W R budgetRead ∧
                                                        Cont budgetRead E terminalRead ∧
                                                          Cont terminalRead H matureRead ∧
                                                            PkgSig bundle matureRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro lUnary kUnary jUnary sUnary wUnary rUnary eUnary hUnary sealRoute classifierRoute
    witnessRoute budgetRoute terminalRoute matureRoute maturePkg
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed lUnary kUnary sealRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed sealUnary jUnary classifierRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed classifierUnary sUnary witnessRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed wUnary rUnary budgetRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetUnary eUnary terminalRoute
  have matureUnary : UnaryHistory matureRead :=
    unary_cont_closed terminalUnary hUnary matureRoute
  exact
    ⟨rfl, sealUnary, classifierUnary, witnessUnary, budgetUnary, terminalUnary,
      matureUnary, sealRoute, classifierRoute, witnessRoute, budgetRoute, terminalRoute,
      matureRoute, maturePkg⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
