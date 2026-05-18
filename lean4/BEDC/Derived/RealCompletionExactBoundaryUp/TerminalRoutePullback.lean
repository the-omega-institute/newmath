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

theorem RealCompletionExactBoundaryTerminalRoutePullback [AskSetup] [PackageSetup]
    {L K J S W R D E H C P N sealRead classifierRead witnessRead budgetRead terminalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory K ->
        UnaryHistory J ->
          UnaryHistory S ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory D ->
                  UnaryHistory E ->
                    Cont L K sealRead ->
                      Cont sealRead J classifierRead ->
                        Cont classifierRead S witnessRead ->
                          Cont W R budgetRead ->
                            Cont budgetRead E terminalRead ->
                              PkgSig bundle N pkg ->
                                PkgSig bundle terminalRead pkg ->
                                  realCompletionExactBoundaryFields
                                      (RealCompletionExactBoundaryUp.mk L K J S W R D E H C P N) =
                                    [L, K, J, S, W, R, D, E, H, C, P, N] ∧
                                    UnaryHistory sealRead ∧ UnaryHistory classifierRead ∧
                                      UnaryHistory witnessRead ∧ UnaryHistory budgetRead ∧
                                        UnaryHistory terminalRead ∧ Cont L K sealRead ∧
                                          Cont sealRead J classifierRead ∧
                                            Cont classifierRead S witnessRead ∧
                                              Cont W R budgetRead ∧
                                                Cont budgetRead E terminalRead ∧
                                                  PkgSig bundle N pkg ∧
                                                    PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro unaryL unaryK unaryJ unaryS unaryW unaryR _unaryD unaryE sealCont classifierCont
    witnessCont budgetCont terminalCont namePkg terminalPkg
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unaryL unaryK sealCont
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed sealUnary unaryJ classifierCont
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed classifierUnary unaryS witnessCont
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed unaryW unaryR budgetCont
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetUnary unaryE terminalCont
  exact
    ⟨rfl, sealUnary, classifierUnary, witnessUnary, budgetUnary, terminalUnary, sealCont,
      classifierCont, witnessCont, budgetCont, terminalCont, namePkg, terminalPkg⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
