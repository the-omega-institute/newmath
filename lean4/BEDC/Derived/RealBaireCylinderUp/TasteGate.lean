import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealBaireCylinderUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealBaireCylinderUp : Type where
  | mk (B S Q E H C P N : BHist) : RealBaireCylinderUp
  deriving DecidableEq

def realBaireCylinderEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realBaireCylinderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realBaireCylinderEncodeBHist h

def realBaireCylinderDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realBaireCylinderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realBaireCylinderDecodeBHist tail)

theorem RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realBaireCylinderFields : RealBaireCylinderUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealBaireCylinderUp.mk B S Q E H C P N => [B, S, Q, E, H, C, P, N]

def realBaireCylinderToEventFlow : RealBaireCylinderUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realBaireCylinderFields x).map realBaireCylinderEncodeBHist

def realBaireCylinderFromEventFlow : EventFlow -> Option RealBaireCylinderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
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
                                        (RealBaireCylinderUp.mk
                                          (realBaireCylinderDecodeBHist B)
                                          (realBaireCylinderDecodeBHist S)
                                          (realBaireCylinderDecodeBHist Q)
                                          (realBaireCylinderDecodeBHist E)
                                          (realBaireCylinderDecodeBHist H)
                                          (realBaireCylinderDecodeBHist C)
                                          (realBaireCylinderDecodeBHist P)
                                          (realBaireCylinderDecodeBHist N))
                                  | _ :: _ => none

theorem RealBaireCylinderTasteGate_single_carrier_alignment_round_trip :
    forall x : RealBaireCylinderUp,
      realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B S Q E H C P N =>
      change
        some
          (RealBaireCylinderUp.mk
            (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist B))
            (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist S))
            (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist Q))
            (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist E))
            (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist H))
            (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist C))
            (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist P))
            (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist N))) =
          some (RealBaireCylinderUp.mk B S Q E H C P N)
      rw [RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode B,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode S,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode Q,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode E,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode H,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode C,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode P,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode N]

theorem RealBaireCylinderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealBaireCylinderUp} :
    realBaireCylinderToEventFlow x = realBaireCylinderToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow x) =
        realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow y) :=
    congrArg realBaireCylinderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealBaireCylinderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealBaireCylinderTasteGate_single_carrier_alignment_round_trip y)))

theorem RealBaireCylinderTasteGate_single_carrier_alignment_field_faithful :
    forall x y : RealBaireCylinderUp, realBaireCylinderFields x = realBaireCylinderFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 S1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 S2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realBaireCylinderBHistCarrier : BHistCarrier RealBaireCylinderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realBaireCylinderToEventFlow
  fromEventFlow := realBaireCylinderFromEventFlow

instance realBaireCylinderChapterTasteGate : ChapterTasteGate RealBaireCylinderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow x) = some x
    exact RealBaireCylinderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealBaireCylinderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realBaireCylinderFieldFaithful : FieldFaithful RealBaireCylinderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realBaireCylinderFields
  field_faithful := RealBaireCylinderTasteGate_single_carrier_alignment_field_faithful

instance realBaireCylinderNontrivial : Nontrivial RealBaireCylinderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealBaireCylinderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RealBaireCylinderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealBaireCylinderTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealBaireCylinderUp) ∧
      Nonempty (FieldFaithful RealBaireCylinderUp) ∧
        Nonempty (Nontrivial RealBaireCylinderUp) ∧
          (∀ h : BHist, realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist h) = h) ∧
            (∀ x : RealBaireCylinderUp,
              realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow x) = some x) ∧
              (∀ x y : RealBaireCylinderUp,
                realBaireCylinderToEventFlow x = realBaireCylinderToEventFlow y -> x = y) ∧
                realBaireCylinderEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨realBaireCylinderChapterTasteGate⟩
  · constructor
    · exact ⟨realBaireCylinderFieldFaithful⟩
    · constructor
      · exact ⟨realBaireCylinderNontrivial⟩
      · constructor
        · exact RealBaireCylinderTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact RealBaireCylinderTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact RealBaireCylinderTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.RealBaireCylinderUp.TasteGate
