import BEDC.Derived.CauchyInverseBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyInverseBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def CauchyInverseBudgetRouteSurface
    (X A M W D R S H C P N sourceStep windowStep readbackStep sealStep : BHist) :
  Prop :=
  UnaryHistory X ∧ UnaryHistory A ∧ UnaryHistory M ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory S ∧ Cont X A sourceStep ∧ Cont M W windowStep ∧
      Cont D R readbackStep ∧ Cont readbackStep S sealStep ∧
        ∃ packet : CauchyInverseBudgetUp,
          packet =
            CauchyInverseBudgetUp.mk X A M W D R S H C P N

theorem CauchyInverseBudgetRouteSurface_apartness_window_closure
    {X A M W D R S H C P N sourceStep windowStep readbackStep sealStep : BHist} :
    CauchyInverseBudgetRouteSurface X A M W D R S H C P N sourceStep windowStep
      readbackStep sealStep →
      UnaryHistory S ∧ UnaryHistory sourceStep ∧ UnaryHistory windowStep ∧
        UnaryHistory readbackStep ∧ UnaryHistory sealStep ∧ Cont X A sourceStep ∧
          Cont M W windowStep ∧ Cont D R readbackStep ∧ Cont readbackStep S sealStep ∧
            hsame P P ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont
  intro route
  cases route with
  | intro unaryX routeTail =>
      cases routeTail with
      | intro unaryA routeTail =>
          cases routeTail with
          | intro unaryM routeTail =>
              cases routeTail with
              | intro unaryW routeTail =>
                  cases routeTail with
                  | intro unaryD routeTail =>
                      cases routeTail with
                      | intro unaryR routeTail =>
                          cases routeTail with
                          | intro unaryS routeTail =>
                              cases routeTail with
                              | intro sourceCont routeTail =>
                                  cases routeTail with
                                  | intro windowCont routeTail =>
                                      cases routeTail with
                                      | intro readbackCont routeTail =>
                                          cases routeTail with
                                          | intro sealCont packetWitness =>
                                              cases packetWitness with
                                              | intro packet packetEq =>
                                                  cases packetEq
                                                  have unarySourceStep : UnaryHistory sourceStep :=
                                                    unary_cont_closed unaryX unaryA sourceCont
                                                  have unaryWindowStep : UnaryHistory windowStep :=
                                                    unary_cont_closed unaryM unaryW windowCont
                                                  have unaryReadbackStep :
                                                      UnaryHistory readbackStep :=
                                                    unary_cont_closed unaryD unaryR readbackCont
                                                  have unarySealStep : UnaryHistory sealStep :=
                                                    unary_cont_closed unaryReadbackStep unaryS
                                                      sealCont
                                                  constructor
                                                  · exact unaryS
                                                  · constructor
                                                    · exact unarySourceStep
                                                    · constructor
                                                      · exact unaryWindowStep
                                                      · constructor
                                                        · exact unaryReadbackStep
                                                        · constructor
                                                          · exact unarySealStep
                                                          · constructor
                                                            · exact sourceCont
                                                            · constructor
                                                              · exact windowCont
                                                              · constructor
                                                                · exact readbackCont
                                                                · constructor
                                                                  · exact sealCont
                                                                  · constructor
                                                                    · rfl
                                                                    · rfl

end BEDC.Derived.CauchyInverseBudgetUp
