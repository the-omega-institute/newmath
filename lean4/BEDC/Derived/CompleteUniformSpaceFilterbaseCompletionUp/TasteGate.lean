import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteUniformSpaceFilterbaseCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteUniformSpaceFilterbaseCompletionUp : Type where
  | mk (U F B L S R E H C P N : BHist) : CompleteUniformSpaceFilterbaseCompletionUp
  deriving DecidableEq

def completeUniformSpaceFilterbaseCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeUniformSpaceFilterbaseCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeUniformSpaceFilterbaseCompletionEncodeBHist h

def completeUniformSpaceFilterbaseCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeUniformSpaceFilterbaseCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeUniformSpaceFilterbaseCompletionDecodeBHist tail)

private theorem completeUniformSpaceFilterbaseCompletion_decode_encode_bhist :
    forall h : BHist, completeUniformSpaceFilterbaseCompletionDecodeBHist
      (completeUniformSpaceFilterbaseCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completeUniformSpaceFilterbaseCompletionFields :
    CompleteUniformSpaceFilterbaseCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteUniformSpaceFilterbaseCompletionUp.mk U F B L S R E H C P N =>
      [U, F, B, L, S, R, E, H, C, P, N]

def completeUniformSpaceFilterbaseCompletionToEventFlow :
    CompleteUniformSpaceFilterbaseCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (completeUniformSpaceFilterbaseCompletionFields x).map
        completeUniformSpaceFilterbaseCompletionEncodeBHist

private def completeUniformSpaceFilterbaseCompletionEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      completeUniformSpaceFilterbaseCompletionEventAtDefault index rest

def completeUniformSpaceFilterbaseCompletionFromEventFlow :
    EventFlow -> Option CompleteUniformSpaceFilterbaseCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompleteUniformSpaceFilterbaseCompletionUp.mk
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 0 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 1 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 2 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 3 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 4 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 5 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 6 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 7 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 8 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 9 ef))
        (completeUniformSpaceFilterbaseCompletionDecodeBHist
          (completeUniformSpaceFilterbaseCompletionEventAtDefault 10 ef)))

private theorem completeUniformSpaceFilterbaseCompletion_round_trip :
    forall x : CompleteUniformSpaceFilterbaseCompletionUp,
      completeUniformSpaceFilterbaseCompletionFromEventFlow
        (completeUniformSpaceFilterbaseCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U F B L S R E H C P N =>
      change
        some
          (CompleteUniformSpaceFilterbaseCompletionUp.mk
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist U))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist F))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist B))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist L))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist S))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist R))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist E))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist H))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist C))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist P))
            (completeUniformSpaceFilterbaseCompletionDecodeBHist
              (completeUniformSpaceFilterbaseCompletionEncodeBHist N))) =
          some (CompleteUniformSpaceFilterbaseCompletionUp.mk U F B L S R E H C P N)
      rw [completeUniformSpaceFilterbaseCompletion_decode_encode_bhist U,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist F,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist B,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist L,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist S,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist R,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist E,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist H,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist C,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist P,
        completeUniformSpaceFilterbaseCompletion_decode_encode_bhist N]

private theorem completeUniformSpaceFilterbaseCompletionToEventFlow_injective
    {x y : CompleteUniformSpaceFilterbaseCompletionUp} :
    completeUniformSpaceFilterbaseCompletionToEventFlow x =
        completeUniformSpaceFilterbaseCompletionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeUniformSpaceFilterbaseCompletionFromEventFlow
          (completeUniformSpaceFilterbaseCompletionToEventFlow x) =
        completeUniformSpaceFilterbaseCompletionFromEventFlow
          (completeUniformSpaceFilterbaseCompletionToEventFlow y) :=
    congrArg completeUniformSpaceFilterbaseCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeUniformSpaceFilterbaseCompletion_round_trip x).symm
      (Eq.trans hread (completeUniformSpaceFilterbaseCompletion_round_trip y)))

instance completeUniformSpaceFilterbaseCompletionBHistCarrier :
    BHistCarrier CompleteUniformSpaceFilterbaseCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeUniformSpaceFilterbaseCompletionToEventFlow
  fromEventFlow := completeUniformSpaceFilterbaseCompletionFromEventFlow

instance completeUniformSpaceFilterbaseCompletionChapterTasteGate :
    ChapterTasteGate CompleteUniformSpaceFilterbaseCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      completeUniformSpaceFilterbaseCompletionFromEventFlow
        (completeUniformSpaceFilterbaseCompletionToEventFlow x) = some x
    exact completeUniformSpaceFilterbaseCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completeUniformSpaceFilterbaseCompletionToEventFlow_injective heq)

theorem CompleteUniformSpaceFilterbaseCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist, completeUniformSpaceFilterbaseCompletionDecodeBHist
      (completeUniformSpaceFilterbaseCompletionEncodeBHist h) = h) ∧
      (forall x : CompleteUniformSpaceFilterbaseCompletionUp,
        completeUniformSpaceFilterbaseCompletionFromEventFlow
          (completeUniformSpaceFilterbaseCompletionToEventFlow x) = some x) ∧
        (forall x y : CompleteUniformSpaceFilterbaseCompletionUp,
          completeUniformSpaceFilterbaseCompletionToEventFlow x =
              completeUniformSpaceFilterbaseCompletionToEventFlow y ->
            x = y) ∧
          completeUniformSpaceFilterbaseCompletionEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨completeUniformSpaceFilterbaseCompletion_decode_encode_bhist,
      completeUniformSpaceFilterbaseCompletion_round_trip,
      (fun _ _ heq => completeUniformSpaceFilterbaseCompletionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompleteUniformSpaceFilterbaseCompletionUp
