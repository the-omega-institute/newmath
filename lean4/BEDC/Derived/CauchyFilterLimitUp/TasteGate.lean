import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterLimitUp : Type where
  | mk (B F S R D A H C P N : BHist) : CauchyFilterLimitUp
  deriving DecidableEq

def cauchyFilterLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterLimitEncodeBHist h

def cauchyFilterLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterLimitDecodeBHist tail)

private theorem cauchyFilterLimitDecode_encode_bhist :
    ∀ h : BHist, cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterLimitFields : CauchyFilterLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterLimitUp.mk B F S R D A H C P N => [B, F, S, R, D, A, H, C, P, N]

def cauchyFilterLimitToEventFlow : CauchyFilterLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterLimitUp.mk B F S R D A H C P N =>
      [[BMark.b0, BMark.b1, BMark.b0, BMark.b1],
        cauchyFilterLimitEncodeBHist B,
        cauchyFilterLimitEncodeBHist F,
        cauchyFilterLimitEncodeBHist S,
        cauchyFilterLimitEncodeBHist R,
        cauchyFilterLimitEncodeBHist D,
        cauchyFilterLimitEncodeBHist A,
        cauchyFilterLimitEncodeBHist H,
        cauchyFilterLimitEncodeBHist C,
        cauchyFilterLimitEncodeBHist P,
        cauchyFilterLimitEncodeBHist N]

def cauchyFilterLimitFromEventFlow : EventFlow → Option CauchyFilterLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag, B, F, S, R, D, A, H, C, P, N] =>
      some
        (CauchyFilterLimitUp.mk
          (cauchyFilterLimitDecodeBHist B)
          (cauchyFilterLimitDecodeBHist F)
          (cauchyFilterLimitDecodeBHist S)
          (cauchyFilterLimitDecodeBHist R)
          (cauchyFilterLimitDecodeBHist D)
          (cauchyFilterLimitDecodeBHist A)
          (cauchyFilterLimitDecodeBHist H)
          (cauchyFilterLimitDecodeBHist C)
          (cauchyFilterLimitDecodeBHist P)
          (cauchyFilterLimitDecodeBHist N))
  | _ => none

private theorem cauchyFilterLimit_round_trip :
    ∀ x : CauchyFilterLimitUp,
      cauchyFilterLimitFromEventFlow (cauchyFilterLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B F S R D A H C P N =>
      change
        some
          (CauchyFilterLimitUp.mk
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist B))
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist F))
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist S))
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist R))
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist D))
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist A))
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist H))
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist C))
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist P))
            (cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist N))) =
          some (CauchyFilterLimitUp.mk B F S R D A H C P N)
      rw [cauchyFilterLimitDecode_encode_bhist B, cauchyFilterLimitDecode_encode_bhist F,
        cauchyFilterLimitDecode_encode_bhist S, cauchyFilterLimitDecode_encode_bhist R,
        cauchyFilterLimitDecode_encode_bhist D, cauchyFilterLimitDecode_encode_bhist A,
        cauchyFilterLimitDecode_encode_bhist H, cauchyFilterLimitDecode_encode_bhist C,
        cauchyFilterLimitDecode_encode_bhist P, cauchyFilterLimitDecode_encode_bhist N]

private theorem cauchyFilterLimitToEventFlow_injective {x y : CauchyFilterLimitUp} :
    cauchyFilterLimitToEventFlow x = cauchyFilterLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterLimitFromEventFlow (cauchyFilterLimitToEventFlow x) =
        cauchyFilterLimitFromEventFlow (cauchyFilterLimitToEventFlow y) :=
    congrArg cauchyFilterLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyFilterLimit_round_trip x).symm
      (Eq.trans hread (cauchyFilterLimit_round_trip y)))

private theorem cauchyFilterLimit_fields_faithful :
    ∀ x y : CauchyFilterLimitUp, cauchyFilterLimitFields x = cauchyFilterLimitFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 F1 S1 R1 D1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 F2 S2 R2 D2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyFilterLimitBHistCarrier : BHistCarrier CauchyFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterLimitToEventFlow
  fromEventFlow := cauchyFilterLimitFromEventFlow

instance cauchyFilterLimitChapterTasteGate : ChapterTasteGate CauchyFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterLimitFromEventFlow (cauchyFilterLimitToEventFlow x) = some x
    exact cauchyFilterLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyFilterLimitToEventFlow_injective heq)

instance cauchyFilterLimitFieldFaithful : FieldFaithful CauchyFilterLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyFilterLimitFields
  field_faithful := cauchyFilterLimit_fields_faithful

def taste_gate : ChapterTasteGate CauchyFilterLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterLimitChapterTasteGate

theorem CauchyFilterLimitTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchyFilterLimitDecodeBHist (cauchyFilterLimitEncodeBHist h) = h) ∧
      cauchyFilterLimitFields
          (CauchyFilterLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      cauchyFilterLimitToEventFlow
          (CauchyFilterLimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b0, BMark.b1, BMark.b0, BMark.b1], [], [], [], [], [], [], [], [], [],
          []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact ⟨cauchyFilterLimitDecode_encode_bhist, rfl, rfl⟩

end BEDC.Derived.CauchyFilterLimitUp
