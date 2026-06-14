import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceCriterionUp : Type where
  | mk
      (A M D S R E H C P N : BHist) :
      CauchySequenceCriterionUp

def cauchySequenceCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceCriterionEncodeBHist h

def cauchySequenceCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceCriterionDecodeBHist tail)

private theorem cauchySequenceCriterion_decode_encode_bhist :
    ∀ h : BHist,
      cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySequenceCriterionFields : CauchySequenceCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceCriterionUp.mk A M D S R E H C P N =>
      [A, M, D, S, R, E, H, C, P, N]

def cauchySequenceCriterionToEventFlow : CauchySequenceCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchySequenceCriterionFields x).map cauchySequenceCriterionEncodeBHist

private def cauchySequenceCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySequenceCriterionEventAtDefault index rest

def cauchySequenceCriterionFromEventFlow
    (flow : EventFlow) : Option CauchySequenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySequenceCriterionUp.mk
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 0 flow))
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 1 flow))
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 2 flow))
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 3 flow))
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 4 flow))
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 5 flow))
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 6 flow))
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 7 flow))
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 8 flow))
      (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEventAtDefault 9 flow)))

private theorem cauchySequenceCriterion_round_trip :
    ∀ x : CauchySequenceCriterionUp,
      cauchySequenceCriterionFromEventFlow
        (cauchySequenceCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M D S R E H C P N =>
      change
        some
          (CauchySequenceCriterionUp.mk
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist A))
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist M))
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist D))
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist S))
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist R))
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist E))
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist H))
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist C))
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist P))
            (cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist N))) =
          some (CauchySequenceCriterionUp.mk A M D S R E H C P N)
      rw [cauchySequenceCriterion_decode_encode_bhist A,
        cauchySequenceCriterion_decode_encode_bhist M,
        cauchySequenceCriterion_decode_encode_bhist D,
        cauchySequenceCriterion_decode_encode_bhist S,
        cauchySequenceCriterion_decode_encode_bhist R,
        cauchySequenceCriterion_decode_encode_bhist E,
        cauchySequenceCriterion_decode_encode_bhist H,
        cauchySequenceCriterion_decode_encode_bhist C,
        cauchySequenceCriterion_decode_encode_bhist P,
        cauchySequenceCriterion_decode_encode_bhist N]

private theorem cauchySequenceCriterionToEventFlow_injective
    {x y : CauchySequenceCriterionUp} :
    cauchySequenceCriterionToEventFlow x = cauchySequenceCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceCriterionFromEventFlow (cauchySequenceCriterionToEventFlow x) =
        cauchySequenceCriterionFromEventFlow (cauchySequenceCriterionToEventFlow y) :=
    congrArg cauchySequenceCriterionFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (cauchySequenceCriterion_round_trip x).symm
        (Eq.trans hread (cauchySequenceCriterion_round_trip y)))

instance cauchySequenceCriterionBHistCarrier :
    BHistCarrier CauchySequenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceCriterionToEventFlow
  fromEventFlow := cauchySequenceCriterionFromEventFlow

instance cauchySequenceCriterionChapterTasteGate :
    ChapterTasteGate CauchySequenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySequenceCriterionFromEventFlow
        (cauchySequenceCriterionToEventFlow x) = some x
    exact cauchySequenceCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySequenceCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchySequenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySequenceCriterionChapterTasteGate

theorem CauchySequenceCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchySequenceCriterionDecodeBHist (cauchySequenceCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchySequenceCriterionUp) ∧
        Nonempty (ChapterTasteGate CauchySequenceCriterionUp) ∧
          cauchySequenceCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨cauchySequenceCriterion_decode_encode_bhist,
      ⟨cauchySequenceCriterionBHistCarrier⟩,
      ⟨cauchySequenceCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchySequenceCriterionUp
