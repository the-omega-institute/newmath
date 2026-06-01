import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RankNullityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RankNullityUp : Type where
  | mk (L S T K I A U M H C P N : BHist) : RankNullityUp
  deriving DecidableEq

def rankNullityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rankNullityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rankNullityEncodeBHist h

def rankNullityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rankNullityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rankNullityDecodeBHist tail)

private theorem rankNullityDecode_encode_bhist :
    ∀ h : BHist, rankNullityDecodeBHist (rankNullityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rankNullityFields : RankNullityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RankNullityUp.mk L S T K I A U M H C P N => [L, S, T, K, I, A, U, M, H, C, P, N]

def rankNullityToEventFlow : RankNullityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rankNullityFields x).map rankNullityEncodeBHist

private def rankNullityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rankNullityEventAtDefault index rest

def rankNullityFromEventFlow : EventFlow → Option RankNullityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RankNullityUp.mk
        (rankNullityDecodeBHist (rankNullityEventAtDefault 0 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 1 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 2 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 3 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 4 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 5 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 6 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 7 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 8 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 9 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 10 ef))
        (rankNullityDecodeBHist (rankNullityEventAtDefault 11 ef)))

private theorem rankNullity_round_trip :
    ∀ x : RankNullityUp, rankNullityFromEventFlow (rankNullityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L S T K I A U M H C P N =>
      change
        some
          (RankNullityUp.mk
            (rankNullityDecodeBHist (rankNullityEncodeBHist L))
            (rankNullityDecodeBHist (rankNullityEncodeBHist S))
            (rankNullityDecodeBHist (rankNullityEncodeBHist T))
            (rankNullityDecodeBHist (rankNullityEncodeBHist K))
            (rankNullityDecodeBHist (rankNullityEncodeBHist I))
            (rankNullityDecodeBHist (rankNullityEncodeBHist A))
            (rankNullityDecodeBHist (rankNullityEncodeBHist U))
            (rankNullityDecodeBHist (rankNullityEncodeBHist M))
            (rankNullityDecodeBHist (rankNullityEncodeBHist H))
            (rankNullityDecodeBHist (rankNullityEncodeBHist C))
            (rankNullityDecodeBHist (rankNullityEncodeBHist P))
            (rankNullityDecodeBHist (rankNullityEncodeBHist N))) =
          some (RankNullityUp.mk L S T K I A U M H C P N)
      rw [rankNullityDecode_encode_bhist L, rankNullityDecode_encode_bhist S,
        rankNullityDecode_encode_bhist T, rankNullityDecode_encode_bhist K,
        rankNullityDecode_encode_bhist I, rankNullityDecode_encode_bhist A,
        rankNullityDecode_encode_bhist U, rankNullityDecode_encode_bhist M,
        rankNullityDecode_encode_bhist H, rankNullityDecode_encode_bhist C,
        rankNullityDecode_encode_bhist P, rankNullityDecode_encode_bhist N]

private theorem rankNullityToEventFlow_injective {x y : RankNullityUp} :
    rankNullityToEventFlow x = rankNullityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rankNullityFromEventFlow (rankNullityToEventFlow x) =
        rankNullityFromEventFlow (rankNullityToEventFlow y) :=
    congrArg rankNullityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rankNullity_round_trip x).symm
      (Eq.trans hread (rankNullity_round_trip y)))

instance rankNullityBHistCarrier : BHistCarrier RankNullityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rankNullityToEventFlow
  fromEventFlow := rankNullityFromEventFlow

instance rankNullityChapterTasteGate : ChapterTasteGate RankNullityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rankNullityFromEventFlow (rankNullityToEventFlow x) = some x
    exact rankNullity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rankNullityToEventFlow_injective heq)

theorem RankNullityTasteGate_single_carrier_alignment :
    (forall h : BHist, rankNullityDecodeBHist (rankNullityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RankNullityUp) ∧
        Nonempty (ChapterTasteGate RankNullityUp) ∧
          rankNullityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact rankNullityDecode_encode_bhist
  · constructor
    · exact Nonempty.intro rankNullityBHistCarrier
    · constructor
      · exact Nonempty.intro rankNullityChapterTasteGate
      · rfl

end BEDC.Derived.RankNullityUp
