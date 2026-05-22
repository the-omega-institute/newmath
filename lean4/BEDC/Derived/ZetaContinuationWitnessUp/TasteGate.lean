import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZetaContinuationWitnessUp : Type where
  | mk (B E A P F T G H C R N : BHist) : ZetaContinuationWitnessUp
  deriving DecidableEq

def zetaContinuationWitnessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zetaContinuationWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zetaContinuationWitnessEncodeBHist h

def zetaContinuationWitnessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zetaContinuationWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zetaContinuationWitnessDecodeBHist tail)

private theorem ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def zetaContinuationWitnessFields : ZetaContinuationWitnessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ZetaContinuationWitnessUp.mk B E A P F T G H C R N => [B, E, A, P, F, T, G, H, C, R, N]

def zetaContinuationWitnessToEventFlow : ZetaContinuationWitnessUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (zetaContinuationWitnessFields x).map zetaContinuationWitnessEncodeBHist

def zetaContinuationWitnessFromEventFlow : EventFlow -> Option ZetaContinuationWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | A :: rest2 =>
              match rest2 with
              | [] => none
              | P :: rest3 =>
                  match rest3 with
                  | [] => none
                  | F :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | G :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (ZetaContinuationWitnessUp.mk
                                                      (zetaContinuationWitnessDecodeBHist B)
                                                      (zetaContinuationWitnessDecodeBHist E)
                                                      (zetaContinuationWitnessDecodeBHist A)
                                                      (zetaContinuationWitnessDecodeBHist P)
                                                      (zetaContinuationWitnessDecodeBHist F)
                                                      (zetaContinuationWitnessDecodeBHist T)
                                                      (zetaContinuationWitnessDecodeBHist G)
                                                      (zetaContinuationWitnessDecodeBHist H)
                                                      (zetaContinuationWitnessDecodeBHist C)
                                                      (zetaContinuationWitnessDecodeBHist R)
                                                      (zetaContinuationWitnessDecodeBHist N))
                                              | _ :: _ => none

private theorem ZetaContinuationWitnessTasteGate_single_carrier_alignment_round_trip :
    forall x : ZetaContinuationWitnessUp,
      zetaContinuationWitnessFromEventFlow (zetaContinuationWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B E A P F T G H C R N =>
      change
        some
          (ZetaContinuationWitnessUp.mk
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist B))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist E))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist A))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist P))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist F))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist T))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist G))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist H))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist C))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist R))
            (zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist N))) =
          some (ZetaContinuationWitnessUp.mk B E A P F T G H C R N)
      rw [ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode B,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode E,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode A,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode P,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode F,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode T,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode G,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode H,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode C,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode R,
        ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode N]

private theorem ZetaContinuationWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ZetaContinuationWitnessUp} :
    zetaContinuationWitnessToEventFlow x = zetaContinuationWitnessToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zetaContinuationWitnessFromEventFlow (zetaContinuationWitnessToEventFlow x) =
        zetaContinuationWitnessFromEventFlow (zetaContinuationWitnessToEventFlow y) :=
    congrArg zetaContinuationWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ZetaContinuationWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ZetaContinuationWitnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem ZetaContinuationWitnessTasteGate_single_carrier_alignment_fields :
    forall x y : ZetaContinuationWitnessUp, zetaContinuationWitnessFields x =
      zetaContinuationWitnessFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 E1 A1 P1 F1 T1 G1 H1 C1 R1 N1 =>
      cases y with
      | mk B2 E2 A2 P2 F2 T2 G2 H2 C2 R2 N2 =>
          cases hfields
          rfl

instance zetaContinuationWitnessBHistCarrier : BHistCarrier ZetaContinuationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zetaContinuationWitnessToEventFlow
  fromEventFlow := zetaContinuationWitnessFromEventFlow

instance zetaContinuationWitnessChapterTasteGate : ChapterTasteGate ZetaContinuationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change zetaContinuationWitnessFromEventFlow (zetaContinuationWitnessToEventFlow x) = some x
    exact ZetaContinuationWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ZetaContinuationWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance zetaContinuationWitnessFieldFaithful : FieldFaithful ZetaContinuationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := zetaContinuationWitnessFields
  field_faithful := ZetaContinuationWitnessTasteGate_single_carrier_alignment_fields

instance zetaContinuationWitnessNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ZetaContinuationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ZetaContinuationWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ZetaContinuationWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ZetaContinuationWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  zetaContinuationWitnessChapterTasteGate

namespace TasteGate

theorem ZetaContinuationWitnessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ZetaContinuationWitnessUp) ∧
      Nonempty (FieldFaithful ZetaContinuationWitnessUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ZetaContinuationWitnessUp) ∧
          (∀ h : BHist,
            zetaContinuationWitnessDecodeBHist (zetaContinuationWitnessEncodeBHist h) = h) ∧
            (∀ x : ZetaContinuationWitnessUp,
              zetaContinuationWitnessFromEventFlow (zetaContinuationWitnessToEventFlow x) =
                some x) ∧
              (∀ x y : ZetaContinuationWitnessUp,
                zetaContinuationWitnessToEventFlow x = zetaContinuationWitnessToEventFlow y ->
                  x = y) ∧
                zetaContinuationWitnessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨zetaContinuationWitnessChapterTasteGate⟩
  · constructor
    · exact ⟨zetaContinuationWitnessFieldFaithful⟩
    · constructor
      · exact ⟨zetaContinuationWitnessNontrivial⟩
      · constructor
        · exact ZetaContinuationWitnessTasteGate_single_carrier_alignment_decode
        · constructor
          · exact ZetaContinuationWitnessTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact ZetaContinuationWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

def taste_gate : ChapterTasteGate ZetaContinuationWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.ZetaContinuationWitnessUp.taste_gate

end TasteGate

end BEDC.Derived.ZetaContinuationWitnessUp
