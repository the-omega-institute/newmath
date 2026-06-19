import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirectedSubnetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DirectedSubnetUp : Type where
  | mk (I J phi K L S R D A H C P N : BHist) : DirectedSubnetUp
  deriving DecidableEq

def directedSubnetTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1]

def directedSubnetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: directedSubnetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: directedSubnetEncodeBHist h

def directedSubnetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (directedSubnetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (directedSubnetDecodeBHist tail)

private theorem DirectedSubnetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, directedSubnetDecodeBHist (directedSubnetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def directedSubnetToEventFlow : DirectedSubnetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DirectedSubnetUp.mk I J phi K L S R D A H C P N =>
      [directedSubnetTag,
        directedSubnetEncodeBHist I,
        directedSubnetEncodeBHist J,
        directedSubnetEncodeBHist phi,
        directedSubnetEncodeBHist K,
        directedSubnetEncodeBHist L,
        directedSubnetEncodeBHist S,
        directedSubnetEncodeBHist R,
        directedSubnetEncodeBHist D,
        directedSubnetEncodeBHist A,
        directedSubnetEncodeBHist H,
        directedSubnetEncodeBHist C,
        directedSubnetEncodeBHist P,
        directedSubnetEncodeBHist N]

private def directedSubnetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => directedSubnetEventAt index rest

def directedSubnetFromEventFlow : EventFlow → Option DirectedSubnetUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DirectedSubnetUp.mk
          (directedSubnetDecodeBHist (directedSubnetEventAt 1 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 2 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 3 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 4 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 5 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 6 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 7 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 8 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 9 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 10 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 11 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 12 ef))
          (directedSubnetDecodeBHist (directedSubnetEventAt 13 ef)))

private theorem DirectedSubnetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DirectedSubnetUp, directedSubnetFromEventFlow (directedSubnetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J phi K L S R D A H C P N =>
      change
        some
          (DirectedSubnetUp.mk
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist I))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist J))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist phi))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist K))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist L))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist S))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist R))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist D))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist A))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist H))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist C))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist P))
            (directedSubnetDecodeBHist (directedSubnetEncodeBHist N))) =
          some (DirectedSubnetUp.mk I J phi K L S R D A H C P N)
      rw [DirectedSubnetTasteGate_single_carrier_alignment_decode_encode I,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode J,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode phi,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode K,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode L,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode S,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode R,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode D,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode A,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode H,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode C,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode P,
        DirectedSubnetTasteGate_single_carrier_alignment_decode_encode N]

private theorem directedSubnetToEventFlow_injective {x y : DirectedSubnetUp} :
    directedSubnetToEventFlow x = directedSubnetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      directedSubnetFromEventFlow (directedSubnetToEventFlow x) =
        directedSubnetFromEventFlow (directedSubnetToEventFlow y) :=
    congrArg directedSubnetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DirectedSubnetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DirectedSubnetTasteGate_single_carrier_alignment_round_trip y)))

instance directedSubnetBHistCarrier : BHistCarrier DirectedSubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := directedSubnetToEventFlow
  fromEventFlow := directedSubnetFromEventFlow

instance directedSubnetChapterTasteGate : ChapterTasteGate DirectedSubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change directedSubnetFromEventFlow (directedSubnetToEventFlow x) = some x
    exact DirectedSubnetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (directedSubnetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DirectedSubnetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  directedSubnetChapterTasteGate

theorem DirectedSubnetTasteGate_single_carrier_alignment :
    (∀ h : BHist, directedSubnetDecodeBHist (directedSubnetEncodeBHist h) = h) ∧
      (∀ x : DirectedSubnetUp, directedSubnetFromEventFlow (directedSubnetToEventFlow x) = some x) ∧
        (∀ x y : DirectedSubnetUp, directedSubnetToEventFlow x = directedSubnetToEventFlow y → x = y) ∧
          directedSubnetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DirectedSubnetTasteGate_single_carrier_alignment_decode_encode,
      DirectedSubnetTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact directedSubnetToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DirectedSubnetUp
