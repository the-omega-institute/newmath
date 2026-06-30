import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactApartnessProfileUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactApartnessProfileUp : Type where
  | mk (K T C S F R H E P N : BHist) : CompactApartnessProfileUp
  deriving DecidableEq

def CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist h

def CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
        (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CompactApartnessProfileTasteGate_single_carrier_alignment_fields :
    CompactApartnessProfileUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactApartnessProfileUp.mk K T C S F R H E P N => [K, T, C, S, F, R, H, E, P, N]

def CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow :
    CompactApartnessProfileUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CompactApartnessProfileTasteGate_single_carrier_alignment_fields x).map
      CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist

def CompactApartnessProfileTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CompactApartnessProfileUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | C :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | F :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CompactApartnessProfileUp.mk
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist K)
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist T)
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist C)
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist S)
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist F)
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist R)
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist H)
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist E)
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist P)
                                                  (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist N))
                                          | _ :: _ => none

private theorem CompactApartnessProfileTasteGate_single_carrier_alignment_round_trip :
    forall x : CompactApartnessProfileUp,
      CompactApartnessProfileTasteGate_single_carrier_alignment_fromEventFlow
        (CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K T C S F R H E P N =>
      change
        some
          (CompactApartnessProfileUp.mk
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist K))
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist T))
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist C))
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist S))
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist F))
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist R))
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist H))
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist E))
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist P))
            (CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
              (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CompactApartnessProfileUp.mk K T C S F R H E P N)
      rw [CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode K,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode T,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode C,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode S,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode F,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode R,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode H,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode E,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode P,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactApartnessProfileUp} :
    CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow x =
      CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CompactApartnessProfileTasteGate_single_carrier_alignment_fromEventFlow
          (CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow x) =
        CompactApartnessProfileTasteGate_single_carrier_alignment_fromEventFlow
          (CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CompactApartnessProfileTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactApartnessProfileTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactApartnessProfileTasteGate_single_carrier_alignment_round_trip y)))

instance compactApartnessProfileBHistCarrier : BHistCarrier CompactApartnessProfileUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CompactApartnessProfileTasteGate_single_carrier_alignment_fromEventFlow

instance compactApartnessProfileChapterTasteGate :
    ChapterTasteGate CompactApartnessProfileUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CompactApartnessProfileTasteGate_single_carrier_alignment_fromEventFlow
        (CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
    exact CompactApartnessProfileTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactApartnessProfileUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactApartnessProfileChapterTasteGate

theorem CompactApartnessProfileTasteGate_single_carrier_alignment :
    (forall K T C S F R H E P N : BHist,
      CompactApartnessProfileTasteGate_single_carrier_alignment_fields
        (CompactApartnessProfileUp.mk K T C S F R H E P N) =
          [K, T, C, S, F, R, H, E, P, N]) ∧
      (forall h : BHist,
        CompactApartnessProfileTasteGate_single_carrier_alignment_decodeBHist
          (CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        CompactApartnessProfileTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] ∧
          Nonempty (ChapterTasteGate CompactApartnessProfileUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  have gate : ChapterTasteGate CompactApartnessProfileUp := {
    round_trip := by
      intro x
      change
        CompactApartnessProfileTasteGate_single_carrier_alignment_fromEventFlow
          (CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow x) =
            some x
      exact CompactApartnessProfileTasteGate_single_carrier_alignment_round_trip x
    layer_separation := by
      intro x y hxy heq
      exact hxy (CompactApartnessProfileTasteGate_single_carrier_alignment_toEventFlow_injective heq) }
  constructor
  · intro K T C S F R H E P N
    rfl
  · constructor
    · exact CompactApartnessProfileTasteGate_single_carrier_alignment_decode_encode
    · constructor
      · rfl
      · exact ⟨gate⟩

end BEDC.Derived.CompactApartnessProfileUp
