import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLocallyCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLocallyCompactUp : Type where
  | mk (R U W D B K A H C P N : BHist) : RealLocallyCompactUp
  deriving DecidableEq

def realLocallyCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLocallyCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLocallyCompactEncodeBHist h

def realLocallyCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLocallyCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLocallyCompactDecodeBHist tail)

private theorem realLocallyCompactDecode_encode :
    ∀ h : BHist, realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realLocallyCompactFields : RealLocallyCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealLocallyCompactUp.mk r u w d b k a h c p n => [r, u, w, d, b, k, a, h, c, p, n]

def realLocallyCompactToEventFlow : RealLocallyCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realLocallyCompactFields x).map realLocallyCompactEncodeBHist

private def realLocallyCompactEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realLocallyCompactEventAt index rest

def realLocallyCompactFromEventFlow : EventFlow → Option RealLocallyCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealLocallyCompactUp.mk
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 0 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 1 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 2 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 3 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 4 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 5 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 6 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 7 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 8 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 9 ef))
        (realLocallyCompactDecodeBHist (realLocallyCompactEventAt 10 ef)))

private theorem realLocallyCompact_round_trip :
    ∀ x : RealLocallyCompactUp,
      realLocallyCompactFromEventFlow (realLocallyCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk r u w d b k a h c p n =>
      change
        some
            (RealLocallyCompactUp.mk
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist r))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist u))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist w))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist d))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist b))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist k))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist a))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist h))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist c))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist p))
              (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist n))) =
          some (RealLocallyCompactUp.mk r u w d b k a h c p n)
      rw [realLocallyCompactDecode_encode r, realLocallyCompactDecode_encode u,
        realLocallyCompactDecode_encode w, realLocallyCompactDecode_encode d,
        realLocallyCompactDecode_encode b, realLocallyCompactDecode_encode k,
        realLocallyCompactDecode_encode a, realLocallyCompactDecode_encode h,
        realLocallyCompactDecode_encode c, realLocallyCompactDecode_encode p,
        realLocallyCompactDecode_encode n]

private theorem realLocallyCompactToEventFlow_injective {x y : RealLocallyCompactUp} :
    realLocallyCompactToEventFlow x = realLocallyCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLocallyCompactFromEventFlow (realLocallyCompactToEventFlow x) =
        realLocallyCompactFromEventFlow (realLocallyCompactToEventFlow y) :=
    congrArg realLocallyCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realLocallyCompact_round_trip x).symm
      (Eq.trans hread (realLocallyCompact_round_trip y)))

instance realLocallyCompactBHistCarrier : BHistCarrier RealLocallyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLocallyCompactToEventFlow
  fromEventFlow := realLocallyCompactFromEventFlow

instance realLocallyCompactChapterTasteGate : ChapterTasteGate RealLocallyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := realLocallyCompact_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (realLocallyCompactToEventFlow_injective heq)

namespace TasteGate

theorem RealLocallyCompactTasteGate_single_carrier_alignment :
    (∀ h : BHist, realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist h) = h) ∧
      (∀ x : RealLocallyCompactUp,
        realLocallyCompactFromEventFlow (realLocallyCompactToEventFlow x) = some x) ∧
        (∀ x y : RealLocallyCompactUp,
          realLocallyCompactToEventFlow x = realLocallyCompactToEventFlow y → x = y) ∧
          realLocallyCompactEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact realLocallyCompactDecode_encode
  · constructor
    · exact realLocallyCompact_round_trip
    · constructor
      · intro x y heq
        exact realLocallyCompactToEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.RealLocallyCompactUp
