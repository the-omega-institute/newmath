import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PreRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PreRealUp : Type where
  | mk (D S R H C K N : BHist) : PreRealUp

def preRealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: preRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: preRealEncodeBHist h

def preRealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (preRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (preRealDecodeBHist tail)

private theorem PreRealTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, preRealDecodeBHist (preRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def preRealFields : PreRealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PreRealUp.mk D S R H C K N => [D, S, R, H, C, K, N]

def preRealToEventFlow : PreRealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (preRealFields x).map preRealEncodeBHist

def preRealFromEventFlow : EventFlow -> Option PreRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | H :: rest3 =>
                  match rest3 with
                  | [] => none
                  | C :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
                          match rest5 with
                          | [] => none
                          | N :: rest6 =>
                              match rest6 with
                              | [] =>
                                  some
                                    (PreRealUp.mk
                                      (preRealDecodeBHist D)
                                      (preRealDecodeBHist S)
                                      (preRealDecodeBHist R)
                                      (preRealDecodeBHist H)
                                      (preRealDecodeBHist C)
                                      (preRealDecodeBHist K)
                                      (preRealDecodeBHist N))
                              | _ :: _ => none

private theorem PreRealTasteGate_single_carrier_alignment_round_trip :
    forall x : PreRealUp, preRealFromEventFlow (preRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R H C K N =>
      change
        some
          (PreRealUp.mk
            (preRealDecodeBHist (preRealEncodeBHist D))
            (preRealDecodeBHist (preRealEncodeBHist S))
            (preRealDecodeBHist (preRealEncodeBHist R))
            (preRealDecodeBHist (preRealEncodeBHist H))
            (preRealDecodeBHist (preRealEncodeBHist C))
            (preRealDecodeBHist (preRealEncodeBHist K))
            (preRealDecodeBHist (preRealEncodeBHist N))) =
          some (PreRealUp.mk D S R H C K N)
      rw [PreRealTasteGate_single_carrier_alignment_decode_encode D,
        PreRealTasteGate_single_carrier_alignment_decode_encode S,
        PreRealTasteGate_single_carrier_alignment_decode_encode R,
        PreRealTasteGate_single_carrier_alignment_decode_encode H,
        PreRealTasteGate_single_carrier_alignment_decode_encode C,
        PreRealTasteGate_single_carrier_alignment_decode_encode K,
        PreRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem PreRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PreRealUp} :
    preRealToEventFlow x = preRealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      preRealFromEventFlow (preRealToEventFlow x) =
        preRealFromEventFlow (preRealToEventFlow y) :=
    congrArg preRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PreRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PreRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem PreRealTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : PreRealUp, preRealFields x = preRealFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 S1 R1 H1 C1 K1 N1 =>
      cases y with
      | mk D2 S2 R2 H2 C2 K2 N2 =>
          cases hfields
          rfl

instance preRealBHistCarrier : BHistCarrier PreRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := preRealToEventFlow
  fromEventFlow := preRealFromEventFlow

instance preRealChapterTasteGate : ChapterTasteGate PreRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change preRealFromEventFlow (preRealToEventFlow x) = some x
    exact PreRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PreRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance preRealFieldFaithful : FieldFaithful PreRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := preRealFields
  field_faithful := PreRealTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate PreRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  preRealChapterTasteGate

theorem PreRealTasteGate_single_carrier_alignment :
    (forall h : BHist, preRealDecodeBHist (preRealEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PreRealUp) ∧
        Nonempty (ChapterTasteGate PreRealUp) ∧
          Nonempty (FieldFaithful PreRealUp) ∧
            preRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨PreRealTasteGate_single_carrier_alignment_decode_encode,
      ⟨preRealBHistCarrier⟩,
      ⟨preRealChapterTasteGate⟩,
      ⟨preRealFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.PreRealUp
