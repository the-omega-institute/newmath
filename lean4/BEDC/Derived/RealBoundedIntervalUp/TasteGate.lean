import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealBoundedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealBoundedIntervalUp : Type where
  | packet
      (lower upper order leftWindow rightWindow readback located bracket transport replay
        provenance name : BHist) :
      RealBoundedIntervalUp
  deriving DecidableEq

def realBoundedIntervalEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realBoundedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realBoundedIntervalEncodeBHist h

def realBoundedIntervalDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realBoundedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realBoundedIntervalDecodeBHist tail)

private theorem RealBoundedIntervalTasteGate_single_carrier_alignment_decode :
    forall h : BHist, realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realBoundedIntervalFields : RealBoundedIntervalUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealBoundedIntervalUp.packet lower upper order leftWindow rightWindow readback located bracket
      transport replay provenance name =>
      [lower, upper, order, leftWindow, rightWindow, readback, located, bracket, transport, replay,
        provenance, name]

def realBoundedIntervalToEventFlow : RealBoundedIntervalUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realBoundedIntervalFields x).map realBoundedIntervalEncodeBHist

private def realBoundedIntervalEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realBoundedIntervalEventAt index rest

def realBoundedIntervalFromEventFlow (ef : EventFlow) : Option RealBoundedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealBoundedIntervalUp.packet
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 0 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 1 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 2 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 3 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 4 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 5 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 6 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 7 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 8 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 9 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 10 ef))
      (realBoundedIntervalDecodeBHist (realBoundedIntervalEventAt 11 ef)))

private theorem RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip :
    forall x : RealBoundedIntervalUp,
      realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | packet lower upper order leftWindow rightWindow readback located bracket transport replay
      provenance name =>
      change
        some
          (RealBoundedIntervalUp.packet
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist lower))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist upper))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist order))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist leftWindow))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist rightWindow))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist readback))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist located))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist bracket))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist transport))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist replay))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist provenance))
            (realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist name))) =
          some
            (RealBoundedIntervalUp.packet lower upper order leftWindow rightWindow readback located
              bracket transport replay provenance name)
      rw [RealBoundedIntervalTasteGate_single_carrier_alignment_decode lower,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode upper,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode order,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode leftWindow,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode rightWindow,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode readback,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode located,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode bracket,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode transport,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode replay,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode provenance,
        RealBoundedIntervalTasteGate_single_carrier_alignment_decode name]

private theorem RealBoundedIntervalToEventFlow_injective {x y : RealBoundedIntervalUp} :
    realBoundedIntervalToEventFlow x = realBoundedIntervalToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow x) =
        realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow y) :=
    congrArg realBoundedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance realBoundedIntervalBHistCarrier : BHistCarrier RealBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realBoundedIntervalToEventFlow
  fromEventFlow := realBoundedIntervalFromEventFlow

instance realBoundedIntervalChapterTasteGate : ChapterTasteGate RealBoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow x) = some x
    exact RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealBoundedIntervalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealBoundedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realBoundedIntervalChapterTasteGate

theorem RealBoundedIntervalTasteGate_single_carrier_alignment :
    (forall h : BHist, realBoundedIntervalDecodeBHist (realBoundedIntervalEncodeBHist h) = h) ∧
      (forall x : RealBoundedIntervalUp,
        realBoundedIntervalFromEventFlow (realBoundedIntervalToEventFlow x) = some x) ∧
        (forall x y : RealBoundedIntervalUp,
          realBoundedIntervalToEventFlow x = realBoundedIntervalToEventFlow y -> x = y) ∧
          Nonempty (ChapterTasteGate RealBoundedIntervalUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealBoundedIntervalTasteGate_single_carrier_alignment_decode,
      RealBoundedIntervalTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealBoundedIntervalToEventFlow_injective heq),
      ⟨realBoundedIntervalChapterTasteGate⟩⟩

end BEDC.Derived.RealBoundedIntervalUp
