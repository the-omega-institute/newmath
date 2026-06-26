import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailEvaluationFunctionalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailEvaluationFunctionalUp : Type where
  | mk (R W D Q V S H C P N : BHist) : CauchyTailEvaluationFunctionalUp
  deriving DecidableEq

def cauchyTailEvaluationFunctionalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailEvaluationFunctionalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailEvaluationFunctionalEncodeBHist h

def cauchyTailEvaluationFunctionalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailEvaluationFunctionalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailEvaluationFunctionalDecodeBHist tail)

private theorem cauchyTailEvaluationFunctional_decode_encode_bhist :
    ∀ h : BHist,
      cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailEvaluationFunctionalFields :
    CauchyTailEvaluationFunctionalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailEvaluationFunctionalUp.mk R W D Q V S H C P N =>
      [R, W, D, Q, V, S, H, C, P, N]

def cauchyTailEvaluationFunctionalToEventFlow :
    CauchyTailEvaluationFunctionalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailEvaluationFunctionalFields x).map
      cauchyTailEvaluationFunctionalEncodeBHist

private def cauchyTailEvaluationFunctionalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyTailEvaluationFunctionalEventAtDefault index rest

def cauchyTailEvaluationFunctionalFromEventFlow
    (ef : EventFlow) : Option CauchyTailEvaluationFunctionalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyTailEvaluationFunctionalUp.mk
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 0 ef))
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 1 ef))
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 2 ef))
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 3 ef))
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 4 ef))
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 5 ef))
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 6 ef))
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 7 ef))
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 8 ef))
      (cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEventAtDefault 9 ef)))

private theorem cauchyTailEvaluationFunctional_round_trip :
    ∀ x : CauchyTailEvaluationFunctionalUp,
      cauchyTailEvaluationFunctionalFromEventFlow
        (cauchyTailEvaluationFunctionalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D Q V S H C P N =>
      change
        some
          (CauchyTailEvaluationFunctionalUp.mk
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist R))
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist W))
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist D))
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist Q))
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist V))
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist S))
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist H))
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist C))
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist P))
            (cauchyTailEvaluationFunctionalDecodeBHist
              (cauchyTailEvaluationFunctionalEncodeBHist N))) =
          some (CauchyTailEvaluationFunctionalUp.mk R W D Q V S H C P N)
      rw [cauchyTailEvaluationFunctional_decode_encode_bhist R,
        cauchyTailEvaluationFunctional_decode_encode_bhist W,
        cauchyTailEvaluationFunctional_decode_encode_bhist D,
        cauchyTailEvaluationFunctional_decode_encode_bhist Q,
        cauchyTailEvaluationFunctional_decode_encode_bhist V,
        cauchyTailEvaluationFunctional_decode_encode_bhist S,
        cauchyTailEvaluationFunctional_decode_encode_bhist H,
        cauchyTailEvaluationFunctional_decode_encode_bhist C,
        cauchyTailEvaluationFunctional_decode_encode_bhist P,
        cauchyTailEvaluationFunctional_decode_encode_bhist N]

private theorem cauchyTailEvaluationFunctionalToEventFlow_injective
    {x y : CauchyTailEvaluationFunctionalUp} :
    cauchyTailEvaluationFunctionalToEventFlow x =
      cauchyTailEvaluationFunctionalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailEvaluationFunctionalFromEventFlow
          (cauchyTailEvaluationFunctionalToEventFlow x) =
        cauchyTailEvaluationFunctionalFromEventFlow
          (cauchyTailEvaluationFunctionalToEventFlow y) :=
    congrArg cauchyTailEvaluationFunctionalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailEvaluationFunctional_round_trip x).symm
      (Eq.trans hread (cauchyTailEvaluationFunctional_round_trip y)))

instance cauchyTailEvaluationFunctionalBHistCarrier :
    BHistCarrier CauchyTailEvaluationFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailEvaluationFunctionalToEventFlow
  fromEventFlow := cauchyTailEvaluationFunctionalFromEventFlow

instance cauchyTailEvaluationFunctionalChapterTasteGate :
    ChapterTasteGate CauchyTailEvaluationFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyTailEvaluationFunctionalFromEventFlow
        (cauchyTailEvaluationFunctionalToEventFlow x) = some x
    exact cauchyTailEvaluationFunctional_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailEvaluationFunctionalToEventFlow_injective heq)

def CauchyTailEvaluationFunctionalTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyTailEvaluationFunctionalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailEvaluationFunctionalChapterTasteGate

theorem CauchyTailEvaluationFunctionalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyTailEvaluationFunctionalDecodeBHist
        (cauchyTailEvaluationFunctionalEncodeBHist h) = h) ∧
      cauchyTailEvaluationFunctionalEncodeBHist BHist.Empty = ([] : List BMark) ∧
      Nonempty (BHistCarrier CauchyTailEvaluationFunctionalUp) ∧
      Nonempty (ChapterTasteGate CauchyTailEvaluationFunctionalUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyTailEvaluationFunctional_decode_encode_bhist,
      rfl,
      ⟨cauchyTailEvaluationFunctionalBHistCarrier⟩,
      ⟨cauchyTailEvaluationFunctionalChapterTasteGate⟩⟩

end BEDC.Derived.CauchyTailEvaluationFunctionalUp
