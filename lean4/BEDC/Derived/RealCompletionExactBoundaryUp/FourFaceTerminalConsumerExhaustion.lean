import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryFourFaceTerminalConsumerExhaustion [AskSetup] [PackageSetup]
    {L K J S W R D E H C P N sealClassifier witnessBudget streamReg terminalRead
      fourFaceRead terminalConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory K ->
        UnaryHistory J ->
          UnaryHistory S ->
            UnaryHistory W ->
              UnaryHistory R ->
                UnaryHistory D ->
                  UnaryHistory E ->
                    UnaryHistory N ->
                      Cont L K sealClassifier ->
                        Cont J S witnessBudget ->
                          Cont W R streamReg ->
                            Cont D E terminalRead ->
                              Cont streamReg terminalRead fourFaceRead ->
                                Cont fourFaceRead N terminalConsumer ->
                                  PkgSig bundle terminalConsumer pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row terminalConsumer /\ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row fourFaceRead \/
                                            hsame row terminalConsumer)
                                        (fun row : BHist =>
                                          hsame row terminalConsumer /\
                                            PkgSig bundle terminalConsumer pkg)
                                        hsame /\
                                      UnaryHistory terminalConsumer := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro unaryL unaryK unaryJ unaryS unaryW unaryR unaryD unaryE unaryN sealRoute witnessRoute
    streamRoute terminalRoute fourFaceRoute consumerRoute consumerPkg
  have sealClassifierUnary : UnaryHistory sealClassifier :=
    unary_cont_closed unaryL unaryK sealRoute
  have _witnessBudgetUnary : UnaryHistory witnessBudget :=
    unary_cont_closed unaryJ unaryS witnessRoute
  have streamRegUnary : UnaryHistory streamReg :=
    unary_cont_closed unaryW unaryR streamRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed unaryD unaryE terminalRoute
  have fourFaceReadUnary : UnaryHistory fourFaceRead :=
    unary_cont_closed streamRegUnary terminalReadUnary fourFaceRoute
  have terminalConsumerUnary : UnaryHistory terminalConsumer :=
    unary_cont_closed fourFaceReadUnary unaryN consumerRoute
  have sourceTerminal :
      (fun row : BHist => hsame row terminalConsumer /\ UnaryHistory row)
        terminalConsumer := by
    exact ⟨hsame_refl terminalConsumer, terminalConsumerUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminalConsumer /\ UnaryHistory row)
        (fun row : BHist => hsame row fourFaceRead \/ hsame row terminalConsumer)
        (fun row : BHist => hsame row terminalConsumer /\ PkgSig bundle terminalConsumer pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro terminalConsumer sourceTerminal
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, consumerPkg⟩
    }
  exact ⟨cert, terminalConsumerUnary⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
