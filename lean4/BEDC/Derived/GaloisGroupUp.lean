import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem GaloisGroupAutomorphismPacket_composition_closure
    {source middle target leftAction rightAction composite sourceTarget : BHist} :
    UnaryHistory source ->
      UnaryHistory middle ->
        UnaryHistory target ->
          Cont source middle leftAction ->
            Cont middle target rightAction ->
              Cont source target sourceTarget ->
                Cont leftAction rightAction composite ->
                  UnaryHistory sourceTarget ∧ UnaryHistory composite ∧
                    hsame leftAction (append source middle) ∧
                      hsame rightAction (append middle target) ∧
                        hsame sourceTarget (append source target) ∧
                          hsame composite (append (append source middle)
                            (append middle target)) := by
  intro sourceUnary middleUnary targetUnary leftActionCont rightActionCont sourceTargetCont
    compositeCont
  have leftActionUnary : UnaryHistory leftAction :=
    unary_cont_closed sourceUnary middleUnary leftActionCont
  have rightActionUnary : UnaryHistory rightAction :=
    unary_cont_closed middleUnary targetUnary rightActionCont
  have sourceTargetUnary : UnaryHistory sourceTarget :=
    unary_cont_closed sourceUnary targetUnary sourceTargetCont
  have compositeUnary : UnaryHistory composite :=
    unary_cont_closed leftActionUnary rightActionUnary compositeCont
  have sameComposite :
      hsame composite (append (append source middle) (append middle target)) := by
    cases leftActionCont
    cases rightActionCont
    exact compositeCont
  exact And.intro sourceTargetUnary
    (And.intro compositeUnary
      (And.intro leftActionCont
        (And.intro rightActionCont
          (And.intro sourceTargetCont sameComposite))))

end BEDC.Derived.GaloisGroupUp
