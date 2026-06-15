import BEDC.Derived.ConnectedIntervalUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ConnectedIntervalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ConnectedIntervalCarrier (L R W B S T E H C P N : BHist) : Prop :=
  UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory S ∧
    UnaryHistory E ∧ Cont L W B ∧ Cont B S T ∧ Cont T E N ∧ Cont H C P

theorem ConnectedIntervalCarrier_separation_refusal
    {L R W B S T E H C P N : BHist} :
    ConnectedIntervalCarrier L R W B S T E H C P N ->
      UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory B ∧
        UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory E ∧
          Cont L W B ∧ Cont B S T ∧ Cont T E N := by
  -- BEDC touchpoint anchor: BHist BMark
  intro carrier
  cases carrier with
  | intro unaryL rest =>
      cases rest with
      | intro unaryR rest =>
          cases rest with
          | intro unaryW rest =>
              cases rest with
              | intro unaryS rest =>
                  cases rest with
                  | intro unaryE rest =>
                      cases rest with
                      | intro routeB rest =>
                          cases rest with
                          | intro routeT rest =>
                              cases rest with
                              | intro routeN _routeP =>
                                  have unaryB : UnaryHistory B :=
                                    unary_cont_closed unaryL unaryW routeB
                                  have unaryT : UnaryHistory T :=
                                    unary_cont_closed unaryB unaryS routeT
                                  constructor
                                  · exact unaryL
                                  · constructor
                                    · exact unaryR
                                    · constructor
                                      · exact unaryW
                                      · constructor
                                        · exact unaryB
                                        · constructor
                                          · exact unaryS
                                          · constructor
                                            · exact unaryT
                                            · constructor
                                              · exact unaryE
                                              · constructor
                                                · exact routeB
                                                · constructor
                                                  · exact routeT
                                                  · exact routeN

end BEDC.Derived.ConnectedIntervalUp
