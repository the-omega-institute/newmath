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

theorem RealCompletionExactBoundaryAllRowsNecessary [AskSetup] [PackageSetup]
    {L K J S W R D E H C P N sealRead classifierRead witnessRead budgetRead terminalRead
      secondRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory K ->
        UnaryHistory J ->
          UnaryHistory S ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory D ->
                  UnaryHistory E ->
                    UnaryHistory H ->
                      Cont L K sealRead ->
                        Cont sealRead J classifierRead ->
                          Cont classifierRead S witnessRead ->
                            Cont W R budgetRead ->
                              Cont budgetRead E terminalRead ->
                                Cont terminalRead H secondRead ->
                                  PkgSig bundle secondRead pkg ->
                                    realCompletionExactBoundaryFields
                                        (RealCompletionExactBoundaryUp.mk L K J S W R D E H C P N) =
                                      [L, K, J, S, W, R, D, E, H, C, P, N] ∧
                                      UnaryHistory sealRead ∧
                                        UnaryHistory classifierRead ∧
                                          UnaryHistory witnessRead ∧
                                            UnaryHistory budgetRead ∧
                                              UnaryHistory terminalRead ∧
                                                UnaryHistory secondRead ∧
                                                  PkgSig bundle secondRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro unaryL unaryK unaryJ unaryS _unaryW unaryR _unaryD unaryE unaryH
    sealRoute classifierRoute witnessRoute budgetRoute terminalRoute secondRoute secondPkg
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unaryL unaryK sealRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed sealUnary unaryJ classifierRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed classifierUnary unaryS witnessRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed _unaryW unaryR budgetRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetUnary unaryE terminalRoute
  have secondUnary : UnaryHistory secondRead :=
    unary_cont_closed terminalUnary unaryH secondRoute
  exact ⟨rfl, sealUnary, classifierUnary, witnessUnary, budgetUnary, terminalUnary,
    secondUnary, secondPkg⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
