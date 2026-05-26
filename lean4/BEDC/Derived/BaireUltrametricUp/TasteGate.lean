import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireUltrametricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireUltrametricUp : Type where
  | mk (B M V S H C P N : BHist) : BaireUltrametricUp
  deriving DecidableEq

def baireUltrametricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireUltrametricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireUltrametricEncodeBHist h

def baireUltrametricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireUltrametricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireUltrametricDecodeBHist tail)

private theorem BaireUltrametricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, baireUltrametricDecodeBHist (baireUltrametricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireUltrametricToEventFlow : BaireUltrametricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BaireUltrametricUp.mk B M V S H C P N =>
      [[BMark.b0],
        baireUltrametricEncodeBHist B,
        [BMark.b1, BMark.b0],
        baireUltrametricEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        baireUltrametricEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        baireUltrametricEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        baireUltrametricEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        baireUltrametricEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        baireUltrametricEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        baireUltrametricEncodeBHist N]

private def baireUltrametricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireUltrametricEventAtDefault index rest

def baireUltrametricFromEventFlow (ef : EventFlow) : Option BaireUltrametricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireUltrametricUp.mk
      (baireUltrametricDecodeBHist (baireUltrametricEventAtDefault 1 ef))
      (baireUltrametricDecodeBHist (baireUltrametricEventAtDefault 3 ef))
      (baireUltrametricDecodeBHist (baireUltrametricEventAtDefault 5 ef))
      (baireUltrametricDecodeBHist (baireUltrametricEventAtDefault 7 ef))
      (baireUltrametricDecodeBHist (baireUltrametricEventAtDefault 9 ef))
      (baireUltrametricDecodeBHist (baireUltrametricEventAtDefault 11 ef))
      (baireUltrametricDecodeBHist (baireUltrametricEventAtDefault 13 ef))
      (baireUltrametricDecodeBHist (baireUltrametricEventAtDefault 15 ef)))

private theorem BaireUltrametricTasteGate_single_carrier_alignment_round_trip
    (x : BaireUltrametricUp) :
    baireUltrametricFromEventFlow (baireUltrametricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B M V S H C P N =>
      change
        some
          (BaireUltrametricUp.mk
            (baireUltrametricDecodeBHist (baireUltrametricEncodeBHist B))
            (baireUltrametricDecodeBHist (baireUltrametricEncodeBHist M))
            (baireUltrametricDecodeBHist (baireUltrametricEncodeBHist V))
            (baireUltrametricDecodeBHist (baireUltrametricEncodeBHist S))
            (baireUltrametricDecodeBHist (baireUltrametricEncodeBHist H))
            (baireUltrametricDecodeBHist (baireUltrametricEncodeBHist C))
            (baireUltrametricDecodeBHist (baireUltrametricEncodeBHist P))
            (baireUltrametricDecodeBHist (baireUltrametricEncodeBHist N))) =
          some (BaireUltrametricUp.mk B M V S H C P N)
      rw [BaireUltrametricTasteGate_single_carrier_alignment_decode B,
        BaireUltrametricTasteGate_single_carrier_alignment_decode M,
        BaireUltrametricTasteGate_single_carrier_alignment_decode V,
        BaireUltrametricTasteGate_single_carrier_alignment_decode S,
        BaireUltrametricTasteGate_single_carrier_alignment_decode H,
        BaireUltrametricTasteGate_single_carrier_alignment_decode C,
        BaireUltrametricTasteGate_single_carrier_alignment_decode P,
        BaireUltrametricTasteGate_single_carrier_alignment_decode N]

private theorem BaireUltrametricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireUltrametricUp} :
    baireUltrametricToEventFlow x = baireUltrametricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireUltrametricFromEventFlow (baireUltrametricToEventFlow x) =
        baireUltrametricFromEventFlow (baireUltrametricToEventFlow y) :=
    congrArg baireUltrametricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BaireUltrametricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireUltrametricTasteGate_single_carrier_alignment_round_trip y)))

private def baireUltrametricFields : BaireUltrametricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireUltrametricUp.mk B M V S H C P N => [B, M, V, S, H, C, P, N]

private theorem BaireUltrametricTasteGate_single_carrier_alignment_fields :
    ∀ x y : BaireUltrametricUp, baireUltrametricFields x = baireUltrametricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 M1 V1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 M2 V2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance baireUltrametricBHistCarrier : BHistCarrier BaireUltrametricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireUltrametricToEventFlow
  fromEventFlow := baireUltrametricFromEventFlow

instance baireUltrametricChapterTasteGate : ChapterTasteGate BaireUltrametricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireUltrametricFromEventFlow (baireUltrametricToEventFlow x) = some x
    exact BaireUltrametricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireUltrametricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance baireUltrametricFieldFaithful : FieldFaithful BaireUltrametricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := baireUltrametricFields
  field_faithful := BaireUltrametricTasteGate_single_carrier_alignment_fields

instance baireUltrametricNontrivial : Nontrivial BaireUltrametricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireUltrametricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireUltrametricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BaireUltrametricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  baireUltrametricChapterTasteGate

theorem BaireUltrametricTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BaireUltrametricUp) ∧
      Nonempty (FieldFaithful BaireUltrametricUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BaireUltrametricUp) ∧
          (∀ h : BHist,
            baireUltrametricDecodeBHist (baireUltrametricEncodeBHist h) = h) ∧
            (∀ x : BaireUltrametricUp,
              baireUltrametricFromEventFlow (baireUltrametricToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨baireUltrametricChapterTasteGate⟩,
      ⟨baireUltrametricFieldFaithful⟩,
      ⟨baireUltrametricNontrivial⟩,
      BaireUltrametricTasteGate_single_carrier_alignment_decode,
      BaireUltrametricTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.BaireUltrametricUp
