import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusContinuityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusContinuityUp : Type where
  | mk (G S K D Q R H C P N : BHist) : ModulusContinuityUp
  deriving DecidableEq

def modulusContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusContinuityEncodeBHist h

def modulusContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusContinuityDecodeBHist tail)

private theorem modulusContinuityDecode_encode_bhist :
    ∀ h : BHist,
      modulusContinuityDecodeBHist (modulusContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def modulusContinuityFields : ModulusContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusContinuityUp.mk G S K D Q R H C P N => [G, S, K, D, Q, R, H, C, P, N]

def modulusContinuityToEventFlow : ModulusContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusContinuityUp.mk G S K D Q R H C P N =>
      [[BMark.b0],
        modulusContinuityEncodeBHist G,
        [BMark.b1, BMark.b0],
        modulusContinuityEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        modulusContinuityEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusContinuityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusContinuityEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusContinuityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusContinuityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        modulusContinuityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        modulusContinuityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        modulusContinuityEncodeBHist N]

private def modulusContinuityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => modulusContinuityRawAt n rest

private def modulusContinuityLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => modulusContinuityLengthEq n rest

def modulusContinuityFromEventFlow : EventFlow → Option ModulusContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match modulusContinuityLengthEq 20 flow with
      | true =>
          some
            (ModulusContinuityUp.mk
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 1 flow))
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 3 flow))
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 5 flow))
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 7 flow))
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 9 flow))
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 11 flow))
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 13 flow))
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 15 flow))
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 17 flow))
              (modulusContinuityDecodeBHist (modulusContinuityRawAt 19 flow)))
      | false => none

private theorem modulusContinuity_round_trip :
    ∀ x : ModulusContinuityUp,
      modulusContinuityFromEventFlow (modulusContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G S K D Q R H C P N =>
      change
        some
          (ModulusContinuityUp.mk
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist G))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist S))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist K))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist D))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist Q))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist R))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist H))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist C))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist P))
            (modulusContinuityDecodeBHist (modulusContinuityEncodeBHist N))) =
          some (ModulusContinuityUp.mk G S K D Q R H C P N)
      rw [modulusContinuityDecode_encode_bhist G, modulusContinuityDecode_encode_bhist S,
        modulusContinuityDecode_encode_bhist K, modulusContinuityDecode_encode_bhist D,
        modulusContinuityDecode_encode_bhist Q, modulusContinuityDecode_encode_bhist R,
        modulusContinuityDecode_encode_bhist H, modulusContinuityDecode_encode_bhist C,
        modulusContinuityDecode_encode_bhist P, modulusContinuityDecode_encode_bhist N]

private theorem modulusContinuityToEventFlow_injective {x y : ModulusContinuityUp} :
    modulusContinuityToEventFlow x = modulusContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusContinuityFromEventFlow (modulusContinuityToEventFlow x) =
        modulusContinuityFromEventFlow (modulusContinuityToEventFlow y) :=
    congrArg modulusContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (modulusContinuity_round_trip x).symm
      (Eq.trans hread (modulusContinuity_round_trip y)))

private theorem modulusContinuity_field_faithful :
    ∀ x y : ModulusContinuityUp,
      modulusContinuityFields x = modulusContinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G1 S1 K1 D1 Q1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk G2 S2 K2 D2 Q2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance modulusContinuityBHistCarrier : BHistCarrier ModulusContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusContinuityToEventFlow
  fromEventFlow := modulusContinuityFromEventFlow

instance modulusContinuityChapterTasteGate : ChapterTasteGate ModulusContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change modulusContinuityFromEventFlow (modulusContinuityToEventFlow x) = some x
    exact modulusContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (modulusContinuityToEventFlow_injective heq)

instance modulusContinuityFieldFaithful : FieldFaithful ModulusContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := modulusContinuityFields
  field_faithful := modulusContinuity_field_faithful

instance modulusContinuityNontrivial : Nontrivial ModulusContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ModulusContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ModulusContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ModulusContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modulusContinuityChapterTasteGate

theorem ModulusContinuityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ModulusContinuityUp) ∧
      Nonempty (FieldFaithful ModulusContinuityUp) ∧
        Nonempty (Nontrivial ModulusContinuityUp) ∧
          (∀ h : BHist,
            modulusContinuityDecodeBHist (modulusContinuityEncodeBHist h) = h) ∧
            (∀ x : ModulusContinuityUp,
              modulusContinuityFromEventFlow (modulusContinuityToEventFlow x) = some x) ∧
              (∀ x y : ModulusContinuityUp,
                modulusContinuityToEventFlow x = modulusContinuityToEventFlow y → x = y) ∧
                modulusContinuityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨⟨modulusContinuityChapterTasteGate⟩, ⟨modulusContinuityFieldFaithful⟩,
      ⟨modulusContinuityNontrivial⟩, modulusContinuityDecode_encode_bhist,
      modulusContinuity_round_trip, (fun _ _ heq => modulusContinuityToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ModulusContinuityUp.TasteGate

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

theorem ModulusContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.modulusContinuityDecodeBHist
          (TasteGate.modulusContinuityEncodeBHist h) =
        h) ∧
      (∀ x : TasteGate.ModulusContinuityUp,
        TasteGate.modulusContinuityFromEventFlow
            (TasteGate.modulusContinuityToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGate.ModulusContinuityUp,
          TasteGate.modulusContinuityToEventFlow x =
              TasteGate.modulusContinuityToEventFlow y →
            x = y) ∧
          TasteGate.modulusContinuityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨TasteGate.ModulusContinuityTasteGate_single_carrier_alignment.2.2.2.1,
      TasteGate.ModulusContinuityTasteGate_single_carrier_alignment.2.2.2.2.1,
      TasteGate.ModulusContinuityTasteGate_single_carrier_alignment.2.2.2.2.2.1,
      TasteGate.ModulusContinuityTasteGate_single_carrier_alignment.2.2.2.2.2.2⟩

end BEDC.Derived.ModulusContinuityUp
