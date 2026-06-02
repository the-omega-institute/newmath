import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionCriterionUp : Type where
  | mk (M W R K U E H C P N : BHist) : BishopCompletionCriterionUp
  deriving DecidableEq

def bishopCompletionCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionCriterionEncodeBHist h

def bishopCompletionCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionCriterionDecodeBHist tail)

private theorem bishopCompletionCriterion_decode_encode_bhist :
    ∀ h : BHist,
      bishopCompletionCriterionDecodeBHist
        (bishopCompletionCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopCompletionCriterionFields :
    BishopCompletionCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionCriterionUp.mk M W R K U E H C P N => [M, W, R, K, U, E, H, C, P, N]

def bishopCompletionCriterionToEventFlow :
    BishopCompletionCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (bishopCompletionCriterionFields token).map bishopCompletionCriterionEncodeBHist

private def bishopCompletionCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompletionCriterionEventAt index rest

def bishopCompletionCriterionFromEventFlow :
    EventFlow → Option BishopCompletionCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (BishopCompletionCriterionUp.mk
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 0 flow))
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 1 flow))
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 2 flow))
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 3 flow))
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 4 flow))
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 5 flow))
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 6 flow))
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 7 flow))
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 8 flow))
          (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEventAt 9 flow)))

private theorem bishopCompletionCriterion_round_trip :
    ∀ x : BishopCompletionCriterionUp,
      bishopCompletionCriterionFromEventFlow
        (bishopCompletionCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M W R K U E H C P N =>
      change
        some
          (BishopCompletionCriterionUp.mk
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist M))
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist W))
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist R))
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist K))
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist U))
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist E))
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist H))
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist C))
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist P))
            (bishopCompletionCriterionDecodeBHist (bishopCompletionCriterionEncodeBHist N))) =
          some (BishopCompletionCriterionUp.mk M W R K U E H C P N)
      rw [bishopCompletionCriterion_decode_encode_bhist M,
        bishopCompletionCriterion_decode_encode_bhist W,
        bishopCompletionCriterion_decode_encode_bhist R,
        bishopCompletionCriterion_decode_encode_bhist K,
        bishopCompletionCriterion_decode_encode_bhist U,
        bishopCompletionCriterion_decode_encode_bhist E,
        bishopCompletionCriterion_decode_encode_bhist H,
        bishopCompletionCriterion_decode_encode_bhist C,
        bishopCompletionCriterion_decode_encode_bhist P,
        bishopCompletionCriterion_decode_encode_bhist N]

private theorem bishopCompletionCriterionToEventFlow_injective
    {x y : BishopCompletionCriterionUp} :
    bishopCompletionCriterionToEventFlow x =
      bishopCompletionCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionCriterionFromEventFlow (bishopCompletionCriterionToEventFlow x) =
        bishopCompletionCriterionFromEventFlow (bishopCompletionCriterionToEventFlow y) :=
    congrArg bishopCompletionCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCompletionCriterion_round_trip x).symm
      (Eq.trans hread (bishopCompletionCriterion_round_trip y)))

instance bishopCompletionCriterionBHistCarrier :
    BHistCarrier BishopCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionCriterionToEventFlow
  fromEventFlow := bishopCompletionCriterionFromEventFlow

instance bishopCompletionCriterionChapterTasteGate :
    ChapterTasteGate BishopCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCompletionCriterionFromEventFlow
        (bishopCompletionCriterionToEventFlow x) = some x
    exact bishopCompletionCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCompletionCriterionToEventFlow_injective heq)

theorem BishopCompletionCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCompletionCriterionDecodeBHist
        (bishopCompletionCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopCompletionCriterionUp) ∧
        Nonempty (ChapterTasteGate BishopCompletionCriterionUp) ∧
          bishopCompletionCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact bishopCompletionCriterion_decode_encode_bhist
  · constructor
    · exact ⟨bishopCompletionCriterionBHistCarrier⟩
    · constructor
      · exact ⟨bishopCompletionCriterionChapterTasteGate⟩
      · rfl

end BEDC.Derived.BishopCompletionCriterionUp
