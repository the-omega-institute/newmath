import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverTraceKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverTraceKernelUp : Type where
  | mk : (H T Q O L C P N : BHist) → ObserverTraceKernelUp
  deriving DecidableEq

def observerTraceKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerTraceKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerTraceKernelEncodeBHist h

def observerTraceKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerTraceKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerTraceKernelDecodeBHist tail)

private theorem observerTraceKernelDecodeEncodeBHist :
    ∀ h : BHist, observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observerTraceKernelFields : ObserverTraceKernelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverTraceKernelUp.mk H T Q O L C P N => [H, T, Q, O, L, C, P, N]

def observerTraceKernelToEventFlow : ObserverTraceKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (observerTraceKernelFields x).map observerTraceKernelEncodeBHist

def observerTraceKernelFromEventFlow : EventFlow → Option ObserverTraceKernelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | H :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | O :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (ObserverTraceKernelUp.mk
                                          (observerTraceKernelDecodeBHist H)
                                          (observerTraceKernelDecodeBHist T)
                                          (observerTraceKernelDecodeBHist Q)
                                          (observerTraceKernelDecodeBHist O)
                                          (observerTraceKernelDecodeBHist L)
                                          (observerTraceKernelDecodeBHist C)
                                          (observerTraceKernelDecodeBHist P)
                                          (observerTraceKernelDecodeBHist N))
                                  | _ :: _ => none

private theorem observerTraceKernel_round_trip :
    ∀ x : ObserverTraceKernelUp,
      observerTraceKernelFromEventFlow (observerTraceKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H T Q O L C P N =>
      change
        some
          (ObserverTraceKernelUp.mk
            (observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist H))
            (observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist T))
            (observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist Q))
            (observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist O))
            (observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist L))
            (observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist C))
            (observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist P))
            (observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist N))) =
          some (ObserverTraceKernelUp.mk H T Q O L C P N)
      rw [observerTraceKernelDecodeEncodeBHist H, observerTraceKernelDecodeEncodeBHist T,
        observerTraceKernelDecodeEncodeBHist Q, observerTraceKernelDecodeEncodeBHist O,
        observerTraceKernelDecodeEncodeBHist L, observerTraceKernelDecodeEncodeBHist C,
        observerTraceKernelDecodeEncodeBHist P, observerTraceKernelDecodeEncodeBHist N]

private theorem observerTraceKernelToEventFlow_injective {x y : ObserverTraceKernelUp} :
    observerTraceKernelToEventFlow x = observerTraceKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerTraceKernelFromEventFlow (observerTraceKernelToEventFlow x) =
        observerTraceKernelFromEventFlow (observerTraceKernelToEventFlow y) :=
    congrArg observerTraceKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerTraceKernel_round_trip x).symm
      (Eq.trans hread (observerTraceKernel_round_trip y)))

private theorem observerTraceKernel_fields_faithful :
    ∀ x y : ObserverTraceKernelUp,
      observerTraceKernelFields x = observerTraceKernelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ T₁ Q₁ O₁ L₁ C₁ P₁ N₁ =>
      cases y with
      | mk H₂ T₂ Q₂ O₂ L₂ C₂ P₂ N₂ =>
          injection hfields with hH tail0
          injection tail0 with hT tail1
          injection tail1 with hQ tail2
          injection tail2 with hO tail3
          injection tail3 with hL tail4
          injection tail4 with hC tail5
          injection tail5 with hP tail6
          injection tail6 with hN _
          subst hH
          subst hT
          subst hQ
          subst hO
          subst hL
          subst hC
          subst hP
          subst hN
          rfl

instance observerTraceKernelBHistCarrier : BHistCarrier ObserverTraceKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerTraceKernelToEventFlow
  fromEventFlow := observerTraceKernelFromEventFlow

instance observerTraceKernelChapterTasteGate : ChapterTasteGate ObserverTraceKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerTraceKernelFromEventFlow (observerTraceKernelToEventFlow x) = some x
    exact observerTraceKernel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerTraceKernelToEventFlow_injective heq)

instance observerTraceKernelFieldFaithful : FieldFaithful ObserverTraceKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerTraceKernelFields
  field_faithful := observerTraceKernel_fields_faithful

def taste_gate : ChapterTasteGate ObserverTraceKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerTraceKernelChapterTasteGate

theorem ObserverTraceKernelTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerTraceKernelDecodeBHist (observerTraceKernelEncodeBHist h) = h) ∧
      (∀ x : ObserverTraceKernelUp,
        observerTraceKernelFromEventFlow (observerTraceKernelToEventFlow x) = some x) ∧
        (∀ x y : ObserverTraceKernelUp,
          observerTraceKernelToEventFlow x = observerTraceKernelToEventFlow y → x = y) ∧
          observerTraceKernelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerTraceKernelDecodeEncodeBHist
  · constructor
    · exact observerTraceKernel_round_trip
    · constructor
      · intro x y heq
        exact observerTraceKernelToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObserverTraceKernelUp
