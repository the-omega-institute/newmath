import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TopologicalClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TopologicalClosureUp : Type where
  | mk (T S x U B W R E H C P N : BHist) : TopologicalClosureUp
  deriving DecidableEq

def topologicalClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: topologicalClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: topologicalClosureEncodeBHist h

def topologicalClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (topologicalClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (topologicalClosureDecodeBHist tail)

private theorem TopologicalClosureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, topologicalClosureDecodeBHist (topologicalClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def TopologicalClosureTasteGate_single_carrier_alignment_fields :
    TopologicalClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TopologicalClosureUp.mk T S x U B W R E H C P N =>
      [T, S, x, U, B, W, R, E, H, C, P, N]

def topologicalClosureToEventFlow : TopologicalClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (TopologicalClosureTasteGate_single_carrier_alignment_fields x).map
      topologicalClosureEncodeBHist

private def topologicalClosureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => topologicalClosureEventAt index rest

def topologicalClosureFromEventFlow (ef : EventFlow) : Option TopologicalClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TopologicalClosureUp.mk
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 0 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 1 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 2 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 3 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 4 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 5 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 6 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 7 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 8 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 9 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 10 ef))
      (topologicalClosureDecodeBHist (topologicalClosureEventAt 11 ef)))

private theorem TopologicalClosureTasteGate_single_carrier_alignment_round_trip
    (x : TopologicalClosureUp) :
    topologicalClosureFromEventFlow (topologicalClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T S x U B W R E H C P N =>
      change
        some
          (TopologicalClosureUp.mk
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist T))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist S))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist x))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist U))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist B))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist W))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist R))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist E))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist H))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist C))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist P))
            (topologicalClosureDecodeBHist (topologicalClosureEncodeBHist N))) =
          some (TopologicalClosureUp.mk T S x U B W R E H C P N)
      rw [TopologicalClosureTasteGate_single_carrier_alignment_decode_encode T,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode S,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode x,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode U,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode B,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode W,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode R,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode E,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode H,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode C,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode P,
        TopologicalClosureTasteGate_single_carrier_alignment_decode_encode N]

private theorem TopologicalClosureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TopologicalClosureUp} :
    topologicalClosureToEventFlow x = topologicalClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      topologicalClosureFromEventFlow (topologicalClosureToEventFlow x) =
        topologicalClosureFromEventFlow (topologicalClosureToEventFlow y) :=
    congrArg topologicalClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TopologicalClosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TopologicalClosureTasteGate_single_carrier_alignment_round_trip y)))

instance topologicalClosureBHistCarrier : BHistCarrier TopologicalClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := topologicalClosureToEventFlow
  fromEventFlow := topologicalClosureFromEventFlow

instance topologicalClosureChapterTasteGate : ChapterTasteGate TopologicalClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change topologicalClosureFromEventFlow (topologicalClosureToEventFlow x) = some x
    exact TopologicalClosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TopologicalClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem TopologicalClosureTasteGate_single_carrier_alignment :
    (∀ h : BHist, topologicalClosureDecodeBHist (topologicalClosureEncodeBHist h) = h) ∧
      (∀ x : TopologicalClosureUp,
        topologicalClosureFromEventFlow (topologicalClosureToEventFlow x) = some x) ∧
        (∀ x y : TopologicalClosureUp,
          topologicalClosureToEventFlow x = topologicalClosureToEventFlow y → x = y) ∧
          topologicalClosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨TopologicalClosureTasteGate_single_carrier_alignment_decode_encode,
      TopologicalClosureTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        TopologicalClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.TopologicalClosureUp
