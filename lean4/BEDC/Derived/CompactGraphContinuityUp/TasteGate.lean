import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactGraphContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactGraphContinuityUp : Type where
  | mk (K F Gamma M Q W R U H C P N : BHist) : CompactGraphContinuityUp
  deriving DecidableEq

def compactGraphContinuityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactGraphContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactGraphContinuityEncodeBHist h

def compactGraphContinuityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactGraphContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactGraphContinuityDecodeBHist tail)

private theorem compactGraphContinuity_decode_encode :
    forall h : BHist,
      compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactGraphContinuityFields : CompactGraphContinuityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactGraphContinuityUp.mk K F Gamma M Q W R U H C P N =>
      [K, F, Gamma, M, Q, W, R, U, H, C, P, N]

def compactGraphContinuityToEventFlow : CompactGraphContinuityUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactGraphContinuityFields x).map compactGraphContinuityEncodeBHist

private def compactGraphContinuityEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactGraphContinuityEventAtDefault index rest

def compactGraphContinuityFromEventFlow : EventFlow -> Option CompactGraphContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactGraphContinuityUp.mk
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 0 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 1 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 2 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 3 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 4 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 5 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 6 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 7 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 8 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 9 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 10 ef))
        (compactGraphContinuityDecodeBHist (compactGraphContinuityEventAtDefault 11 ef)))

private theorem compactGraphContinuity_round_trip :
    forall x : CompactGraphContinuityUp,
      compactGraphContinuityFromEventFlow (compactGraphContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F Gamma M Q W R U H C P N =>
      change
        some
          (CompactGraphContinuityUp.mk
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist K))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist F))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist Gamma))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist M))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist Q))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist W))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist R))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist U))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist H))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist C))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist P))
            (compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist N))) =
          some (CompactGraphContinuityUp.mk K F Gamma M Q W R U H C P N)
      rw [compactGraphContinuity_decode_encode K, compactGraphContinuity_decode_encode F,
        compactGraphContinuity_decode_encode Gamma, compactGraphContinuity_decode_encode M,
        compactGraphContinuity_decode_encode Q, compactGraphContinuity_decode_encode W,
        compactGraphContinuity_decode_encode R, compactGraphContinuity_decode_encode U,
        compactGraphContinuity_decode_encode H, compactGraphContinuity_decode_encode C,
        compactGraphContinuity_decode_encode P, compactGraphContinuity_decode_encode N]

private theorem compactGraphContinuityToEventFlow_injective {x y : CompactGraphContinuityUp} :
    compactGraphContinuityToEventFlow x = compactGraphContinuityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactGraphContinuityFromEventFlow (compactGraphContinuityToEventFlow x) =
        compactGraphContinuityFromEventFlow (compactGraphContinuityToEventFlow y) :=
    congrArg compactGraphContinuityFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans (compactGraphContinuity_round_trip x).symm
      (Eq.trans hread (compactGraphContinuity_round_trip y))
  cases hsome
  rfl

instance compactGraphContinuityBHistCarrier : BHistCarrier CompactGraphContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactGraphContinuityToEventFlow
  fromEventFlow := compactGraphContinuityFromEventFlow

instance compactGraphContinuityChapterTasteGate :
    ChapterTasteGate CompactGraphContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactGraphContinuityFromEventFlow (compactGraphContinuityToEventFlow x) = some x
    exact compactGraphContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactGraphContinuityToEventFlow_injective heq)

theorem CompactGraphContinuityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      compactGraphContinuityDecodeBHist (compactGraphContinuityEncodeBHist h) = h) ∧
      (forall x : CompactGraphContinuityUp,
        compactGraphContinuityFromEventFlow (compactGraphContinuityToEventFlow x) = some x) ∧
        (forall x y : CompactGraphContinuityUp,
          compactGraphContinuityToEventFlow x = compactGraphContinuityToEventFlow y -> x = y) ∧
          compactGraphContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨compactGraphContinuity_decode_encode, compactGraphContinuity_round_trip,
      fun _ _ heq => compactGraphContinuityToEventFlow_injective heq, rfl⟩

end BEDC.Derived.CompactGraphContinuityUp
