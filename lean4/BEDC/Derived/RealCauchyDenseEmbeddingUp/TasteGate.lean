import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyDenseEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyDenseEmbeddingUp : Type where
  | mk (R W D J S H C P N : BHist) : RealCauchyDenseEmbeddingUp
  deriving DecidableEq

def realCauchyDenseEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyDenseEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyDenseEmbeddingEncodeBHist h

def realCauchyDenseEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyDenseEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyDenseEmbeddingDecodeBHist tail)

private theorem RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyDenseEmbeddingFields : RealCauchyDenseEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyDenseEmbeddingUp.mk R W D J S H C P N => [R, W, D, J, S, H, C, P, N]

def realCauchyDenseEmbeddingToEventFlow : RealCauchyDenseEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realCauchyDenseEmbeddingFields x).map realCauchyDenseEmbeddingEncodeBHist

private def realCauchyDenseEmbeddingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCauchyDenseEmbeddingEventAtDefault index rest

def realCauchyDenseEmbeddingFromEventFlow (ef : EventFlow) :
    Option RealCauchyDenseEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCauchyDenseEmbeddingUp.mk
      (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAtDefault 0 ef))
      (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAtDefault 1 ef))
      (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAtDefault 2 ef))
      (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAtDefault 3 ef))
      (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAtDefault 4 ef))
      (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAtDefault 5 ef))
      (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAtDefault 6 ef))
      (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAtDefault 7 ef))
      (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEventAtDefault 8 ef)))

private theorem realCauchyDenseEmbedding_round_trip :
    ∀ x : RealCauchyDenseEmbeddingUp,
      realCauchyDenseEmbeddingFromEventFlow (realCauchyDenseEmbeddingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D J S H C P N =>
      change
        some
            (RealCauchyDenseEmbeddingUp.mk
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist R))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist W))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist D))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist J))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist S))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist H))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist C))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist P))
              (realCauchyDenseEmbeddingDecodeBHist (realCauchyDenseEmbeddingEncodeBHist N))) =
          some (RealCauchyDenseEmbeddingUp.mk R W D J S H C P N)
      rw [RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode R,
        RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode W,
        RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode D,
        RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode J,
        RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode S,
        RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode H,
        RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode C,
        RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode P,
        RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode N]

private theorem realCauchyDenseEmbeddingToEventFlow_injective
    {x y : RealCauchyDenseEmbeddingUp} :
    realCauchyDenseEmbeddingToEventFlow x = realCauchyDenseEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyDenseEmbeddingFromEventFlow (realCauchyDenseEmbeddingToEventFlow x) =
        realCauchyDenseEmbeddingFromEventFlow (realCauchyDenseEmbeddingToEventFlow y) :=
    congrArg realCauchyDenseEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyDenseEmbedding_round_trip x).symm
      (Eq.trans hread (realCauchyDenseEmbedding_round_trip y)))

instance realCauchyDenseEmbeddingBHistCarrier : BHistCarrier RealCauchyDenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyDenseEmbeddingToEventFlow
  fromEventFlow := realCauchyDenseEmbeddingFromEventFlow

instance realCauchyDenseEmbeddingChapterTasteGate :
    ChapterTasteGate RealCauchyDenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCauchyDenseEmbeddingFromEventFlow (realCauchyDenseEmbeddingToEventFlow x) =
      some x
    exact realCauchyDenseEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyDenseEmbeddingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCauchyDenseEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyDenseEmbeddingChapterTasteGate

theorem RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist, realCauchyDenseEmbeddingDecodeBHist
      (realCauchyDenseEmbeddingEncodeBHist h) = h) ∧
      (∀ x : RealCauchyDenseEmbeddingUp,
        realCauchyDenseEmbeddingFromEventFlow (realCauchyDenseEmbeddingToEventFlow x) =
          some x) ∧
        (∀ x y : RealCauchyDenseEmbeddingUp,
          realCauchyDenseEmbeddingToEventFlow x =
            realCauchyDenseEmbeddingToEventFlow y → x = y) ∧
          realCauchyDenseEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealCauchyDenseEmbeddingTasteGate_single_carrier_alignment_decode,
      realCauchyDenseEmbedding_round_trip,
      (fun _ _ heq => realCauchyDenseEmbeddingToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealCauchyDenseEmbeddingUp
