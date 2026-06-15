import BEDC.Derived.AuditMapRouteCompilerUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AuditMapRouteCompilerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def AuditMapRouteCompilerCarrier (E S G A T C M F L H K P _N : BHist) : Prop :=
  UnaryHistory E ∧ UnaryHistory S ∧ UnaryHistory A ∧ UnaryHistory C ∧
    UnaryHistory F ∧ Cont E S G ∧ Cont G A T ∧ Cont T C M ∧ Cont M F L ∧
      Cont H K P

theorem AuditMapRouteCompilerCarrier_nonescape
    {E S G A T C M F L H K P N : BHist} :
    AuditMapRouteCompilerCarrier E S G A T C M F L H K P N ->
      UnaryHistory E ∧ UnaryHistory S ∧ UnaryHistory G ∧ UnaryHistory A ∧
        UnaryHistory T ∧ UnaryHistory C ∧ UnaryHistory M ∧ UnaryHistory F ∧
          UnaryHistory L ∧ Cont E S G ∧ Cont G A T ∧ Cont T C M ∧
            Cont M F L ∧ Cont H K P := by
  -- BEDC touchpoint anchor: BHist BMark
  intro carrier
  cases carrier with
  | intro unaryE rest =>
      cases rest with
      | intro unaryS rest =>
          cases rest with
          | intro unaryA rest =>
              cases rest with
              | intro unaryC rest =>
                  cases rest with
                  | intro unaryF rest =>
                      cases rest with
                      | intro routeG rest =>
                          cases rest with
                          | intro routeT rest =>
                              cases rest with
                              | intro routeM rest =>
                                  cases rest with
                                  | intro routeL routeP =>
                                      have unaryG : UnaryHistory G :=
                                        unary_cont_closed unaryE unaryS routeG
                                      have unaryT : UnaryHistory T :=
                                        unary_cont_closed unaryG unaryA routeT
                                      have unaryM : UnaryHistory M :=
                                        unary_cont_closed unaryT unaryC routeM
                                      have unaryL : UnaryHistory L :=
                                        unary_cont_closed unaryM unaryF routeL
                                      constructor
                                      · exact unaryE
                                      · constructor
                                        · exact unaryS
                                        · constructor
                                          · exact unaryG
                                          · constructor
                                            · exact unaryA
                                            · constructor
                                              · exact unaryT
                                              · constructor
                                                · exact unaryC
                                                · constructor
                                                  · exact unaryM
                                                  · constructor
                                                    · exact unaryF
                                                    · constructor
                                                      · exact unaryL
                                                      · constructor
                                                        · exact routeG
                                                        · constructor
                                                          · exact routeT
                                                          · constructor
                                                            · exact routeM
                                                            · constructor
                                                              · exact routeL
                                                              · exact routeP

end BEDC.Derived.AuditMapRouteCompilerUp
