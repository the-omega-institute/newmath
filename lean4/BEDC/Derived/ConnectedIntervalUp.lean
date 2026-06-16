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

theorem ConnectedIntervalObligationClosureRoute
    {L R W B S T E H C P N «seal» : BHist} :
    ConnectedIntervalCarrier L R W B S T E H C P N ->
      Cont E N «seal» ->
        UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory B ∧
          UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory E ∧ UnaryHistory «seal» ∧
            Cont L W B ∧ Cont B S T ∧ Cont T E N ∧ Cont E N «seal» := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier endpointSeal
  have exposure :=
    ConnectedIntervalCarrier_separation_refusal
      (L := L) (R := R) (W := W) (B := B) (S := S) (T := T) (E := E)
      (H := H) (C := C) (P := P) (N := N) carrier
  obtain ⟨unaryL, unaryR, unaryW, unaryB, unaryS, unaryT, unaryE, routeB, routeT,
    routeN⟩ := exposure
  have unarySeal : UnaryHistory «seal» :=
    unary_cont_closed unaryE (unary_cont_closed unaryT unaryE routeN) endpointSeal
  exact
    ⟨unaryL, unaryR, unaryW, unaryB, unaryS, unaryT, unaryE, unarySeal, routeB,
      routeT, routeN, endpointSeal⟩

end BEDC.Derived.ConnectedIntervalUp
