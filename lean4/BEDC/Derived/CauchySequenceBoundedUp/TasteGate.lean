import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceBoundedUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceBoundedUp : Type where
  | mk (S M D R E B H C P N : BHist) : CauchySequenceBoundedUp
  deriving DecidableEq

def cauchySequenceBoundedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceBoundedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceBoundedEncodeBHist h

def cauchySequenceBoundedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceBoundedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceBoundedDecodeBHist tail)

private theorem cauchySequenceBoundedDecode_encode_bhist :
    ∀ h : BHist,
      cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceBoundedFields : CauchySequenceBoundedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceBoundedUp.mk S M D R E B H C P N => [S, M, D, R, E, B, H, C, P, N]

def cauchySequenceBoundedToEventFlow : CauchySequenceBoundedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceBoundedUp.mk S M D R E B H C P N =>
      [[BMark.b0, BMark.b1, BMark.b1, BMark.b0],
        cauchySequenceBoundedEncodeBHist S,
        cauchySequenceBoundedEncodeBHist M,
        cauchySequenceBoundedEncodeBHist D,
        cauchySequenceBoundedEncodeBHist R,
        cauchySequenceBoundedEncodeBHist E,
        cauchySequenceBoundedEncodeBHist B,
        cauchySequenceBoundedEncodeBHist H,
        cauchySequenceBoundedEncodeBHist C,
        cauchySequenceBoundedEncodeBHist P,
        cauchySequenceBoundedEncodeBHist N]

def cauchySequenceBoundedFromEventFlow : EventFlow → Option CauchySequenceBoundedUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag, S, M, D, R, E, B, H, C, P, N] =>
      some
        (CauchySequenceBoundedUp.mk
          (cauchySequenceBoundedDecodeBHist S)
          (cauchySequenceBoundedDecodeBHist M)
          (cauchySequenceBoundedDecodeBHist D)
          (cauchySequenceBoundedDecodeBHist R)
          (cauchySequenceBoundedDecodeBHist E)
          (cauchySequenceBoundedDecodeBHist B)
          (cauchySequenceBoundedDecodeBHist H)
          (cauchySequenceBoundedDecodeBHist C)
          (cauchySequenceBoundedDecodeBHist P)
          (cauchySequenceBoundedDecodeBHist N))
  | _ => none

private theorem cauchySequenceBounded_round_trip :
    ∀ x : CauchySequenceBoundedUp,
      cauchySequenceBoundedFromEventFlow (cauchySequenceBoundedToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D R E B H C P N =>
      change
        some
          (CauchySequenceBoundedUp.mk
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist S))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist M))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist D))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist R))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist E))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist B))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist H))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist C))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist P))
            (cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist N))) =
          some (CauchySequenceBoundedUp.mk S M D R E B H C P N)
      rw [cauchySequenceBoundedDecode_encode_bhist S,
        cauchySequenceBoundedDecode_encode_bhist M,
        cauchySequenceBoundedDecode_encode_bhist D,
        cauchySequenceBoundedDecode_encode_bhist R,
        cauchySequenceBoundedDecode_encode_bhist E,
        cauchySequenceBoundedDecode_encode_bhist B,
        cauchySequenceBoundedDecode_encode_bhist H,
        cauchySequenceBoundedDecode_encode_bhist C,
        cauchySequenceBoundedDecode_encode_bhist P,
        cauchySequenceBoundedDecode_encode_bhist N]

private theorem cauchySequenceBoundedToEventFlow_injective {x y : CauchySequenceBoundedUp} :
    cauchySequenceBoundedToEventFlow x = cauchySequenceBoundedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceBoundedFromEventFlow (cauchySequenceBoundedToEventFlow x) =
        cauchySequenceBoundedFromEventFlow (cauchySequenceBoundedToEventFlow y) :=
    congrArg cauchySequenceBoundedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySequenceBounded_round_trip x).symm
      (Eq.trans hread (cauchySequenceBounded_round_trip y)))

private theorem cauchySequenceBounded_fields_faithful :
    ∀ x y : CauchySequenceBoundedUp,
      cauchySequenceBoundedFields x = cauchySequenceBoundedFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 M1 D1 R1 E1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 M2 D2 R2 E2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchySequenceBoundedBHistCarrier : BHistCarrier CauchySequenceBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceBoundedToEventFlow
  fromEventFlow := cauchySequenceBoundedFromEventFlow

instance cauchySequenceBoundedChapterTasteGate :
    ChapterTasteGate CauchySequenceBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySequenceBoundedFromEventFlow (cauchySequenceBoundedToEventFlow x) = some x
    exact cauchySequenceBounded_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySequenceBoundedToEventFlow_injective heq)

instance cauchySequenceBoundedFieldFaithful : FieldFaithful CauchySequenceBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySequenceBoundedFields
  field_faithful := cauchySequenceBounded_fields_faithful

def taste_gate : ChapterTasteGate CauchySequenceBoundedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySequenceBoundedChapterTasteGate

theorem CauchySequenceBoundedTasteGate_single_carrier_alignment :
    (forall h : BHist,
        cauchySequenceBoundedDecodeBHist (cauchySequenceBoundedEncodeBHist h) = h) ∧
      cauchySequenceBoundedFields
          (CauchySequenceBoundedUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      cauchySequenceBoundedToEventFlow
          (CauchySequenceBoundedUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b0, BMark.b1, BMark.b1, BMark.b0], [], [], [], [], [], [], [], [], [],
          []] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact ⟨cauchySequenceBoundedDecode_encode_bhist, rfl, rfl⟩

end BEDC.Derived.CauchySequenceBoundedUp
