import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicPartitionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicPartitionUp : Type where
  | mk (B I A R F H C G N : BHist) : DyadicPartitionUp
  deriving DecidableEq

def dyadicPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicPartitionEncodeBHist h

def dyadicPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicPartitionDecodeBHist tail)

private theorem dyadicPartitionDecode_encode_bhist :
    ∀ h : BHist, dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicPartitionToEventFlow : DyadicPartitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicPartitionUp.mk B I A R F H C G N =>
      [dyadicPartitionEncodeBHist B, dyadicPartitionEncodeBHist I,
        dyadicPartitionEncodeBHist A, dyadicPartitionEncodeBHist R,
        dyadicPartitionEncodeBHist F, dyadicPartitionEncodeBHist H,
        dyadicPartitionEncodeBHist C, dyadicPartitionEncodeBHist G,
        dyadicPartitionEncodeBHist N]

def dyadicPartitionFromEventFlow : EventFlow → Option DyadicPartitionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | A :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | F :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | G :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (DyadicPartitionUp.mk
                                              (dyadicPartitionDecodeBHist B)
                                              (dyadicPartitionDecodeBHist I)
                                              (dyadicPartitionDecodeBHist A)
                                              (dyadicPartitionDecodeBHist R)
                                              (dyadicPartitionDecodeBHist F)
                                              (dyadicPartitionDecodeBHist H)
                                              (dyadicPartitionDecodeBHist C)
                                              (dyadicPartitionDecodeBHist G)
                                              (dyadicPartitionDecodeBHist N))
                                      | _ :: _ => none

private def dyadicPartitionFields : DyadicPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicPartitionUp.mk B I A R F H C G N => [B, I, A, R, F, H, C, G, N]

private theorem dyadicPartition_round_trip :
    ∀ x : DyadicPartitionUp,
      dyadicPartitionFromEventFlow (dyadicPartitionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B I A R F H C G N =>
      change
        some
          (DyadicPartitionUp.mk
            (dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist B))
            (dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist I))
            (dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist A))
            (dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist R))
            (dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist F))
            (dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist H))
            (dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist C))
            (dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist G))
            (dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist N))) =
          some (DyadicPartitionUp.mk B I A R F H C G N)
      rw [dyadicPartitionDecode_encode_bhist B, dyadicPartitionDecode_encode_bhist I,
        dyadicPartitionDecode_encode_bhist A, dyadicPartitionDecode_encode_bhist R,
        dyadicPartitionDecode_encode_bhist F, dyadicPartitionDecode_encode_bhist H,
        dyadicPartitionDecode_encode_bhist C, dyadicPartitionDecode_encode_bhist G,
        dyadicPartitionDecode_encode_bhist N]

private theorem dyadicPartitionToEventFlow_injective {x y : DyadicPartitionUp} :
    dyadicPartitionToEventFlow x = dyadicPartitionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicPartitionFromEventFlow (dyadicPartitionToEventFlow x) =
        dyadicPartitionFromEventFlow (dyadicPartitionToEventFlow y) :=
    congrArg dyadicPartitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicPartition_round_trip x).symm
      (Eq.trans hread (dyadicPartition_round_trip y)))

private theorem dyadicPartition_field_faithful :
    ∀ x y : DyadicPartitionUp, dyadicPartitionFields x = dyadicPartitionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 I1 A1 R1 F1 H1 C1 G1 N1 =>
      cases y with
      | mk B2 I2 A2 R2 F2 H2 C2 G2 N2 =>
          cases hfields
          rfl

instance dyadicPartitionBHistCarrier : BHistCarrier DyadicPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicPartitionToEventFlow
  fromEventFlow := dyadicPartitionFromEventFlow

instance dyadicPartitionChapterTasteGate : ChapterTasteGate DyadicPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicPartitionFromEventFlow (dyadicPartitionToEventFlow x) = some x
    exact dyadicPartition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicPartitionToEventFlow_injective heq)

instance dyadicPartitionFieldFaithful : FieldFaithful DyadicPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicPartitionFields
  field_faithful := dyadicPartition_field_faithful

instance dyadicPartitionNontrivial : BEDC.Meta.TasteGate.Nontrivial DyadicPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicPartitionChapterTasteGate

theorem DyadicPartitionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicPartitionUp) ∧
      Nonempty (FieldFaithful DyadicPartitionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicPartitionUp) ∧
          (∀ h : BHist, dyadicPartitionDecodeBHist (dyadicPartitionEncodeBHist h) = h) ∧
            (∀ x : DyadicPartitionUp,
              dyadicPartitionFromEventFlow (dyadicPartitionToEventFlow x) = some x) ∧
              (∀ x y : DyadicPartitionUp,
                dyadicPartitionToEventFlow x = dyadicPartitionToEventFlow y → x = y) ∧
                dyadicPartitionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨⟨dyadicPartitionChapterTasteGate⟩, ⟨dyadicPartitionFieldFaithful⟩,
      ⟨dyadicPartitionNontrivial⟩, dyadicPartitionDecode_encode_bhist,
      dyadicPartition_round_trip, (fun _ _ heq => dyadicPartitionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicPartitionUp.TasteGate
