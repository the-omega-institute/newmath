import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HalfOpenRealIntervalUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HalfOpenRealIntervalUp : Type where
  | mk (L U O D W R E A B H C P N : BHist) : HalfOpenRealIntervalUp
  deriving DecidableEq

def halfOpenRealIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: halfOpenRealIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: halfOpenRealIntervalEncodeBHist h

def halfOpenRealIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (halfOpenRealIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (halfOpenRealIntervalDecodeBHist tail)

private theorem halfOpenRealIntervalDecode_encode :
    ∀ h : BHist, halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def halfOpenRealIntervalFields : HalfOpenRealIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HalfOpenRealIntervalUp.mk L U O D W R E A B H C P N =>
      [L, U, O, D, W, R, E, A, B, H, C, P, N]

def halfOpenRealIntervalToEventFlow : HalfOpenRealIntervalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (halfOpenRealIntervalFields x).map halfOpenRealIntervalEncodeBHist

private def halfOpenRealIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => halfOpenRealIntervalEventAtDefault index rest

def halfOpenRealIntervalFromEventFlow (ef : EventFlow) :
    Option HalfOpenRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HalfOpenRealIntervalUp.mk
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 0 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 1 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 2 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 3 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 4 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 5 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 6 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 7 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 8 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 9 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 10 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 11 ef))
      (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEventAtDefault 12 ef)))

private theorem halfOpenRealInterval_round_trip :
    ∀ x : HalfOpenRealIntervalUp,
      halfOpenRealIntervalFromEventFlow (halfOpenRealIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U O D W R E A B H C P N =>
      change
        some
          (HalfOpenRealIntervalUp.mk
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist L))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist U))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist O))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist D))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist W))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist R))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist E))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist A))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist B))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist H))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist C))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist P))
            (halfOpenRealIntervalDecodeBHist (halfOpenRealIntervalEncodeBHist N))) =
          some (HalfOpenRealIntervalUp.mk L U O D W R E A B H C P N)
      rw [halfOpenRealIntervalDecode_encode L, halfOpenRealIntervalDecode_encode U,
        halfOpenRealIntervalDecode_encode O, halfOpenRealIntervalDecode_encode D,
        halfOpenRealIntervalDecode_encode W, halfOpenRealIntervalDecode_encode R,
        halfOpenRealIntervalDecode_encode E, halfOpenRealIntervalDecode_encode A,
        halfOpenRealIntervalDecode_encode B, halfOpenRealIntervalDecode_encode H,
        halfOpenRealIntervalDecode_encode C, halfOpenRealIntervalDecode_encode P,
        halfOpenRealIntervalDecode_encode N]

private theorem halfOpenRealIntervalToEventFlow_injective
    {x y : HalfOpenRealIntervalUp} :
    halfOpenRealIntervalToEventFlow x = halfOpenRealIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      halfOpenRealIntervalFromEventFlow (halfOpenRealIntervalToEventFlow x) =
        halfOpenRealIntervalFromEventFlow (halfOpenRealIntervalToEventFlow y) :=
    congrArg halfOpenRealIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (halfOpenRealInterval_round_trip x).symm
      (Eq.trans hread (halfOpenRealInterval_round_trip y)))

instance halfOpenRealIntervalBHistCarrier : BHistCarrier HalfOpenRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := halfOpenRealIntervalToEventFlow
  fromEventFlow := halfOpenRealIntervalFromEventFlow

instance halfOpenRealIntervalChapterTasteGate :
    ChapterTasteGate HalfOpenRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change halfOpenRealIntervalFromEventFlow (halfOpenRealIntervalToEventFlow x) = some x
    exact halfOpenRealInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (halfOpenRealIntervalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HalfOpenRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  halfOpenRealIntervalChapterTasteGate

theorem HalfOpenRealIntervalTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier HalfOpenRealIntervalUp) ∧
      Nonempty (ChapterTasteGate HalfOpenRealIntervalUp) ∧
        (∀ x : HalfOpenRealIntervalUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          halfOpenRealIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨halfOpenRealIntervalBHistCarrier⟩
  · constructor
    · exact ⟨halfOpenRealIntervalChapterTasteGate⟩
    · constructor
      · intro x
        change halfOpenRealIntervalFromEventFlow (halfOpenRealIntervalToEventFlow x) = some x
        exact halfOpenRealInterval_round_trip x
      · rfl

end TasteGate
end BEDC.Derived.HalfOpenRealIntervalUp
