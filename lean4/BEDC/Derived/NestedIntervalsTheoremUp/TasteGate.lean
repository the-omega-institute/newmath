import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalsTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalsTheoremUp : Type where
  | mk (B J D W R E H C P N : BHist) : NestedIntervalsTheoremUp
  deriving DecidableEq

def nestedIntervalsTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalsTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalsTheoremEncodeBHist h

def nestedIntervalsTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalsTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalsTheoremDecodeBHist tail)

private theorem NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedIntervalsTheoremFields : NestedIntervalsTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalsTheoremUp.mk B J D W R E H C P N => [B, J, D, W, R, E, H, C, P, N]

def nestedIntervalsTheoremToEventFlow : NestedIntervalsTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nestedIntervalsTheoremFields x).map nestedIntervalsTheoremEncodeBHist

private def nestedIntervalsTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedIntervalsTheoremEventAtDefault index rest

def nestedIntervalsTheoremFromEventFlow :
    EventFlow → Option NestedIntervalsTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (NestedIntervalsTheoremUp.mk
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 0 ef))
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 1 ef))
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 2 ef))
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 3 ef))
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 4 ef))
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 5 ef))
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 6 ef))
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 7 ef))
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 8 ef))
        (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEventAtDefault 9 ef)))

private theorem NestedIntervalsTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NestedIntervalsTheoremUp,
      nestedIntervalsTheoremFromEventFlow (nestedIntervalsTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk B J D W R E H C P N =>
      change
        some
          (NestedIntervalsTheoremUp.mk
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist B))
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist J))
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist D))
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist W))
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist R))
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist E))
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist H))
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist C))
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist P))
            (nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist N))) =
          some (NestedIntervalsTheoremUp.mk B J D W R E H C P N)
      rw [NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode B,
        NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode J,
        NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode D,
        NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode W,
        NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode R,
        NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode E,
        NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode H,
        NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode C,
        NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode P,
        NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem NestedIntervalsTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NestedIntervalsTheoremUp} :
    nestedIntervalsTheoremToEventFlow x = nestedIntervalsTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedIntervalsTheoremFromEventFlow (nestedIntervalsTheoremToEventFlow x) =
        nestedIntervalsTheoremFromEventFlow (nestedIntervalsTheoremToEventFlow y) :=
    congrArg nestedIntervalsTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NestedIntervalsTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NestedIntervalsTheoremTasteGate_single_carrier_alignment_round_trip y)))

private theorem NestedIntervalsTheoremTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : NestedIntervalsTheoremUp,
      nestedIntervalsTheoremFields x = nestedIntervalsTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ J₁ D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ J₂ D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance nestedIntervalsTheoremBHistCarrier :
    BHistCarrier NestedIntervalsTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalsTheoremToEventFlow
  fromEventFlow := nestedIntervalsTheoremFromEventFlow

instance nestedIntervalsTheoremChapterTasteGate :
    ChapterTasteGate NestedIntervalsTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedIntervalsTheoremFromEventFlow (nestedIntervalsTheoremToEventFlow x) = some x
    exact NestedIntervalsTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (NestedIntervalsTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance nestedIntervalsTheoremFieldFaithful :
    FieldFaithful NestedIntervalsTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedIntervalsTheoremFields
  field_faithful :=
    NestedIntervalsTheoremTasteGate_single_carrier_alignment_fields_faithful

instance nestedIntervalsTheoremNontrivial : Nontrivial NestedIntervalsTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedIntervalsTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NestedIntervalsTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem NestedIntervalsTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedIntervalsTheoremDecodeBHist (nestedIntervalsTheoremEncodeBHist h) = h) ∧
      (∀ x : NestedIntervalsTheoremUp,
        nestedIntervalsTheoremFromEventFlow (nestedIntervalsTheoremToEventFlow x) = some x) ∧
        (∀ x y : NestedIntervalsTheoremUp,
          nestedIntervalsTheoremToEventFlow x = nestedIntervalsTheoremToEventFlow y → x = y) ∧
          nestedIntervalsTheoremEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨NestedIntervalsTheoremTasteGate_single_carrier_alignment_decode_encode,
      NestedIntervalsTheoremTasteGate_single_carrier_alignment_round_trip,
      fun _x _y => NestedIntervalsTheoremTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.NestedIntervalsTheoremUp
