import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmptyFableMachineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EmptyFableMachineUp : Type where
  | mk (Z S T L H C P N : BHist) : EmptyFableMachineUp
  deriving DecidableEq

def emptyFableMachineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: emptyFableMachineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: emptyFableMachineEncodeBHist h

def emptyFableMachineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (emptyFableMachineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (emptyFableMachineDecodeBHist tail)

private theorem emptyFableMachineDecode_encode_bhist :
    ∀ h : BHist, emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def emptyFableMachineToEventFlow : EmptyFableMachineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EmptyFableMachineUp.mk Z S T L H C P N =>
      [[BMark.b0], emptyFableMachineEncodeBHist Z, [BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist S, [BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist T, [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist L, [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        emptyFableMachineEncodeBHist N]

def emptyFableMachineFromEventFlow : EventFlow → Option EmptyFableMachineUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | Z :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (EmptyFableMachineUp.mk
                                                                          (emptyFableMachineDecodeBHist Z)
                                                                          (emptyFableMachineDecodeBHist S)
                                                                          (emptyFableMachineDecodeBHist T)
                                                                          (emptyFableMachineDecodeBHist L)
                                                                          (emptyFableMachineDecodeBHist H)
                                                                          (emptyFableMachineDecodeBHist C)
                                                                          (emptyFableMachineDecodeBHist P)
                                                                          (emptyFableMachineDecodeBHist N))
                                                                  | _ :: _ => none

private theorem emptyFableMachine_round_trip :
    ∀ x : EmptyFableMachineUp,
      emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Z S T L H C P N =>
      change
        some
          (EmptyFableMachineUp.mk
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist Z))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist S))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist T))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist L))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist H))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist C))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist P))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist N))) =
          some (EmptyFableMachineUp.mk Z S T L H C P N)
      rw [emptyFableMachineDecode_encode_bhist Z, emptyFableMachineDecode_encode_bhist S,
        emptyFableMachineDecode_encode_bhist T, emptyFableMachineDecode_encode_bhist L,
        emptyFableMachineDecode_encode_bhist H, emptyFableMachineDecode_encode_bhist C,
        emptyFableMachineDecode_encode_bhist P, emptyFableMachineDecode_encode_bhist N]

private theorem emptyFableMachineToEventFlow_injective {x y : EmptyFableMachineUp} :
    emptyFableMachineToEventFlow x = emptyFableMachineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow x) =
        emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow y) :=
    congrArg emptyFableMachineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (emptyFableMachine_round_trip x).symm
      (Eq.trans hread (emptyFableMachine_round_trip y)))

instance emptyFableMachineBHistCarrier : BHistCarrier EmptyFableMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := emptyFableMachineToEventFlow
  fromEventFlow := emptyFableMachineFromEventFlow

instance emptyFableMachineChapterTasteGate : ChapterTasteGate EmptyFableMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow x) = some x
    exact emptyFableMachine_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (emptyFableMachineToEventFlow_injective heq)

instance emptyFableMachineFieldFaithful : FieldFaithful EmptyFableMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | EmptyFableMachineUp.mk Z S T L H C P N => [Z, S, T, L, H, C, P, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk Z S T L H C P N =>
        cases y with
        | mk Z' S' T' L' H' C' P' N' =>
            cases hfields
            rfl

instance emptyFableMachineNontrivial : Nontrivial EmptyFableMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EmptyFableMachineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      EmptyFableMachineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EmptyFableMachineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  emptyFableMachineChapterTasteGate

theorem EmptyFableMachineTasteGate_single_carrier_alignment :
    (∀ h : BHist, emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist h) = h) ∧
      (∀ x : EmptyFableMachineUp,
        emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow x) = some x) ∧
        (∀ x y : EmptyFableMachineUp,
          emptyFableMachineToEventFlow x = emptyFableMachineToEventFlow y → x = y) ∧
          emptyFableMachineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact emptyFableMachineDecode_encode_bhist
  · constructor
    · exact emptyFableMachine_round_trip
    · constructor
      · intro x y heq
        exact emptyFableMachineToEventFlow_injective heq
      · rfl

end BEDC.Derived.EmptyFableMachineUp
