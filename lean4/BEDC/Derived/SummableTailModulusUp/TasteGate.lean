import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SummableTailModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SummableTailModulusUp : Type where
  | mk (M D S R B E H C P N : BHist) : SummableTailModulusUp
  deriving DecidableEq

def summableTailModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: summableTailModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: summableTailModulusEncodeBHist h

def summableTailModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (summableTailModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (summableTailModulusDecodeBHist tail)

private theorem summableTailModulusDecode_encode_bhist :
    ∀ h : BHist,
      summableTailModulusDecodeBHist (summableTailModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def summableTailModulusToEventFlow : SummableTailModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SummableTailModulusUp.mk M D S R B E H C P N =>
      [summableTailModulusEncodeBHist M,
        summableTailModulusEncodeBHist D,
        summableTailModulusEncodeBHist S,
        summableTailModulusEncodeBHist R,
        summableTailModulusEncodeBHist B,
        summableTailModulusEncodeBHist E,
        summableTailModulusEncodeBHist H,
        summableTailModulusEncodeBHist C,
        summableTailModulusEncodeBHist P,
        summableTailModulusEncodeBHist N]

private def summableTailModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => summableTailModulusEventAt index rest

def summableTailModulusFromEventFlow : EventFlow → Option SummableTailModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SummableTailModulusUp.mk
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 0 ef))
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 1 ef))
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 2 ef))
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 3 ef))
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 4 ef))
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 5 ef))
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 6 ef))
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 7 ef))
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 8 ef))
          (summableTailModulusDecodeBHist (summableTailModulusEventAt 9 ef)))

private theorem summableTailModulus_round_trip :
    ∀ x : SummableTailModulusUp,
      summableTailModulusFromEventFlow (summableTailModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D S R B E H C P N =>
      change
        some
          (SummableTailModulusUp.mk
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist M))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist D))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist S))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist R))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist B))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist E))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist H))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist C))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist P))
            (summableTailModulusDecodeBHist (summableTailModulusEncodeBHist N))) =
          some (SummableTailModulusUp.mk M D S R B E H C P N)
      rw [summableTailModulusDecode_encode_bhist M,
        summableTailModulusDecode_encode_bhist D,
        summableTailModulusDecode_encode_bhist S,
        summableTailModulusDecode_encode_bhist R,
        summableTailModulusDecode_encode_bhist B,
        summableTailModulusDecode_encode_bhist E,
        summableTailModulusDecode_encode_bhist H,
        summableTailModulusDecode_encode_bhist C,
        summableTailModulusDecode_encode_bhist P,
        summableTailModulusDecode_encode_bhist N]

private theorem summableTailModulusToEventFlow_injective
    {x y : SummableTailModulusUp} :
    summableTailModulusToEventFlow x = summableTailModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      summableTailModulusFromEventFlow (summableTailModulusToEventFlow x) =
        summableTailModulusFromEventFlow (summableTailModulusToEventFlow y) :=
    congrArg summableTailModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (summableTailModulus_round_trip x).symm
      (Eq.trans hread (summableTailModulus_round_trip y)))

instance summableTailModulusBHistCarrier : BHistCarrier SummableTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := summableTailModulusToEventFlow
  fromEventFlow := summableTailModulusFromEventFlow

instance summableTailModulusChapterTasteGate :
    ChapterTasteGate SummableTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change summableTailModulusFromEventFlow (summableTailModulusToEventFlow x) = some x
    exact summableTailModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (summableTailModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SummableTailModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  summableTailModulusChapterTasteGate

namespace TasteGate

theorem SummableTailModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SummableTailModulusUp) ∧
      (∀ h : BHist,
        summableTailModulusDecodeBHist (summableTailModulusEncodeBHist h) = h) ∧
      (∀ x : SummableTailModulusUp,
        summableTailModulusFromEventFlow (summableTailModulusToEventFlow x) = some x) ∧
      (∀ x y : SummableTailModulusUp,
        summableTailModulusToEventFlow x = summableTailModulusToEventFlow y → x = y) ∧
      summableTailModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨summableTailModulusChapterTasteGate⟩,
      summableTailModulusDecode_encode_bhist,
      summableTailModulus_round_trip,
      (fun _ _ heq => summableTailModulusToEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.SummableTailModulusUp
