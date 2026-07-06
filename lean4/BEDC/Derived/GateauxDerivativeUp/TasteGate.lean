import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GateauxDerivativeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GateauxDerivativeUp : Type where
  | mk (X A V Q T H C P N : BHist) : GateauxDerivativeUp
  deriving DecidableEq

def gateauxDerivativeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gateauxDerivativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gateauxDerivativeEncodeBHist h

def gateauxDerivativeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gateauxDerivativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gateauxDerivativeDecodeBHist tail)

private theorem GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def gateauxDerivativeFields : GateauxDerivativeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GateauxDerivativeUp.mk X A V Q T H C P N => [X, A, V, Q, T, H, C, P, N]

def gateauxDerivativeToEventFlow : GateauxDerivativeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (gateauxDerivativeFields x).map gateauxDerivativeEncodeBHist

private def GateauxDerivativeTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      GateauxDerivativeTasteGate_single_carrier_alignment_eventAt index rest

def gateauxDerivativeFromEventFlow (ef : EventFlow) :
    Option GateauxDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GateauxDerivativeUp.mk
      (gateauxDerivativeDecodeBHist
        (GateauxDerivativeTasteGate_single_carrier_alignment_eventAt 0 ef))
      (gateauxDerivativeDecodeBHist
        (GateauxDerivativeTasteGate_single_carrier_alignment_eventAt 1 ef))
      (gateauxDerivativeDecodeBHist
        (GateauxDerivativeTasteGate_single_carrier_alignment_eventAt 2 ef))
      (gateauxDerivativeDecodeBHist
        (GateauxDerivativeTasteGate_single_carrier_alignment_eventAt 3 ef))
      (gateauxDerivativeDecodeBHist
        (GateauxDerivativeTasteGate_single_carrier_alignment_eventAt 4 ef))
      (gateauxDerivativeDecodeBHist
        (GateauxDerivativeTasteGate_single_carrier_alignment_eventAt 5 ef))
      (gateauxDerivativeDecodeBHist
        (GateauxDerivativeTasteGate_single_carrier_alignment_eventAt 6 ef))
      (gateauxDerivativeDecodeBHist
        (GateauxDerivativeTasteGate_single_carrier_alignment_eventAt 7 ef))
      (gateauxDerivativeDecodeBHist
        (GateauxDerivativeTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem GateauxDerivativeTasteGate_single_carrier_alignment_round_trip
    (x : GateauxDerivativeUp) :
    gateauxDerivativeFromEventFlow (gateauxDerivativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X A V Q T H C P N =>
      change
        some
          (GateauxDerivativeUp.mk
            (gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist X))
            (gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist A))
            (gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist V))
            (gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist Q))
            (gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist T))
            (gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist H))
            (gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist C))
            (gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist P))
            (gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist N))) =
          some (GateauxDerivativeUp.mk X A V Q T H C P N)
      rw [GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode X,
        GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode A,
        GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode V,
        GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode Q,
        GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode T,
        GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode H,
        GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode C,
        GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode P,
        GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode N]

private theorem GateauxDerivativeTasteGate_single_carrier_alignment_injective
    {x y : GateauxDerivativeUp} :
    gateauxDerivativeToEventFlow x = gateauxDerivativeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gateauxDerivativeFromEventFlow (gateauxDerivativeToEventFlow x) =
        gateauxDerivativeFromEventFlow (gateauxDerivativeToEventFlow y) :=
    congrArg gateauxDerivativeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GateauxDerivativeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (GateauxDerivativeTasteGate_single_carrier_alignment_round_trip y)))

instance gateauxDerivativeBHistCarrier :
    BHistCarrier GateauxDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gateauxDerivativeToEventFlow
  fromEventFlow := gateauxDerivativeFromEventFlow

instance gateauxDerivativeChapterTasteGate :
    ChapterTasteGate GateauxDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gateauxDerivativeFromEventFlow (gateauxDerivativeToEventFlow x) = some x
    exact GateauxDerivativeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GateauxDerivativeTasteGate_single_carrier_alignment_injective heq)

theorem GateauxDerivativeTasteGate_single_carrier_alignment :
    (∀ h : BHist, gateauxDerivativeDecodeBHist (gateauxDerivativeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier GateauxDerivativeUp) ∧
        Nonempty (ChapterTasteGate GateauxDerivativeUp) ∧
          gateauxDerivativeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate GateauxDerivativeUp
  constructor
  · exact GateauxDerivativeTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact ⟨gateauxDerivativeBHistCarrier⟩
  constructor
  · exact ⟨gateauxDerivativeChapterTasteGate⟩
  · rfl

end BEDC.Derived.GateauxDerivativeUp
