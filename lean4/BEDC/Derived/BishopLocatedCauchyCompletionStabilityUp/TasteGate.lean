import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedCauchyCompletionStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedCauchyCompletionStabilityUp : Type where
  | mk (D S R L E T C P N : BHist) : BishopLocatedCauchyCompletionStabilityUp
  deriving DecidableEq

def bishopLocatedCauchyCompletionStabilityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedCauchyCompletionStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedCauchyCompletionStabilityEncodeBHist h

def bishopLocatedCauchyCompletionStabilityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedCauchyCompletionStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedCauchyCompletionStabilityDecodeBHist tail)

private theorem bishopLocatedCauchyCompletionStability_decode_encode :
    forall h : BHist,
      bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedCauchyCompletionStabilityFields :
    BishopLocatedCauchyCompletionStabilityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedCauchyCompletionStabilityUp.mk D S R L E T C P N =>
      [D, S, R, L, E, T, C, P, N]

def bishopLocatedCauchyCompletionStabilityToEventFlow :
    BishopLocatedCauchyCompletionStabilityUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopLocatedCauchyCompletionStabilityFields x).map
      bishopLocatedCauchyCompletionStabilityEncodeBHist

private def bishopLocatedCauchyCompletionStabilityEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopLocatedCauchyCompletionStabilityEventAtDefault index rest

def bishopLocatedCauchyCompletionStabilityFromEventFlow
    (ef : EventFlow) : Option BishopLocatedCauchyCompletionStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedCauchyCompletionStabilityUp.mk
      (bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEventAtDefault 0 ef))
      (bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEventAtDefault 1 ef))
      (bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEventAtDefault 2 ef))
      (bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEventAtDefault 3 ef))
      (bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEventAtDefault 4 ef))
      (bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEventAtDefault 5 ef))
      (bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEventAtDefault 6 ef))
      (bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEventAtDefault 7 ef))
      (bishopLocatedCauchyCompletionStabilityDecodeBHist
        (bishopLocatedCauchyCompletionStabilityEventAtDefault 8 ef)))

private theorem bishopLocatedCauchyCompletionStability_round_trip :
    forall x : BishopLocatedCauchyCompletionStabilityUp,
      bishopLocatedCauchyCompletionStabilityFromEventFlow
        (bishopLocatedCauchyCompletionStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R L E T C P N =>
      change
        some
          (BishopLocatedCauchyCompletionStabilityUp.mk
            (bishopLocatedCauchyCompletionStabilityDecodeBHist
              (bishopLocatedCauchyCompletionStabilityEncodeBHist D))
            (bishopLocatedCauchyCompletionStabilityDecodeBHist
              (bishopLocatedCauchyCompletionStabilityEncodeBHist S))
            (bishopLocatedCauchyCompletionStabilityDecodeBHist
              (bishopLocatedCauchyCompletionStabilityEncodeBHist R))
            (bishopLocatedCauchyCompletionStabilityDecodeBHist
              (bishopLocatedCauchyCompletionStabilityEncodeBHist L))
            (bishopLocatedCauchyCompletionStabilityDecodeBHist
              (bishopLocatedCauchyCompletionStabilityEncodeBHist E))
            (bishopLocatedCauchyCompletionStabilityDecodeBHist
              (bishopLocatedCauchyCompletionStabilityEncodeBHist T))
            (bishopLocatedCauchyCompletionStabilityDecodeBHist
              (bishopLocatedCauchyCompletionStabilityEncodeBHist C))
            (bishopLocatedCauchyCompletionStabilityDecodeBHist
              (bishopLocatedCauchyCompletionStabilityEncodeBHist P))
            (bishopLocatedCauchyCompletionStabilityDecodeBHist
              (bishopLocatedCauchyCompletionStabilityEncodeBHist N))) =
          some (BishopLocatedCauchyCompletionStabilityUp.mk D S R L E T C P N)
      rw [bishopLocatedCauchyCompletionStability_decode_encode D,
        bishopLocatedCauchyCompletionStability_decode_encode S,
        bishopLocatedCauchyCompletionStability_decode_encode R,
        bishopLocatedCauchyCompletionStability_decode_encode L,
        bishopLocatedCauchyCompletionStability_decode_encode E,
        bishopLocatedCauchyCompletionStability_decode_encode T,
        bishopLocatedCauchyCompletionStability_decode_encode C,
        bishopLocatedCauchyCompletionStability_decode_encode P,
        bishopLocatedCauchyCompletionStability_decode_encode N]

private theorem bishopLocatedCauchyCompletionStabilityToEventFlow_injective
    {x y : BishopLocatedCauchyCompletionStabilityUp} :
    bishopLocatedCauchyCompletionStabilityToEventFlow x =
      bishopLocatedCauchyCompletionStabilityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedCauchyCompletionStabilityFromEventFlow
          (bishopLocatedCauchyCompletionStabilityToEventFlow x) =
        bishopLocatedCauchyCompletionStabilityFromEventFlow
          (bishopLocatedCauchyCompletionStabilityToEventFlow y) :=
    congrArg bishopLocatedCauchyCompletionStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (bishopLocatedCauchyCompletionStability_round_trip x).symm
      (Eq.trans hread (bishopLocatedCauchyCompletionStability_round_trip y)))

instance bishopLocatedCauchyCompletionStabilityBHistCarrier :
    BHistCarrier BishopLocatedCauchyCompletionStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedCauchyCompletionStabilityToEventFlow
  fromEventFlow := bishopLocatedCauchyCompletionStabilityFromEventFlow

instance bishopLocatedCauchyCompletionStabilityChapterTasteGate :
    ChapterTasteGate BishopLocatedCauchyCompletionStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedCauchyCompletionStabilityFromEventFlow
        (bishopLocatedCauchyCompletionStabilityToEventFlow x) = some x
    exact bishopLocatedCauchyCompletionStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopLocatedCauchyCompletionStabilityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopLocatedCauchyCompletionStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedCauchyCompletionStabilityChapterTasteGate

end BEDC.Derived.BishopLocatedCauchyCompletionStabilityUp
