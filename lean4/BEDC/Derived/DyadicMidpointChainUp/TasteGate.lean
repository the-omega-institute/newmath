import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicMidpointChainUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicMidpointChainUp : Type where
  | mk (L R Q B O W A E H C P N : BHist) : DyadicMidpointChainUp
  deriving DecidableEq

def dyadicMidpointChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicMidpointChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicMidpointChainEncodeBHist h

def dyadicMidpointChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicMidpointChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicMidpointChainDecodeBHist tail)

private theorem DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicMidpointChainFields : DyadicMidpointChainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicMidpointChainUp.mk L R Q B O W A E H C P N =>
      [L, R, Q, B, O, W, A, E, H, C, P, N]

def dyadicMidpointChainToEventFlow : DyadicMidpointChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicMidpointChainFields x).map dyadicMidpointChainEncodeBHist

private def dyadicMidpointChainEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicMidpointChainEventAt index rest

def dyadicMidpointChainFromEventFlow (ef : EventFlow) :
    Option DyadicMidpointChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicMidpointChainUp.mk
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 0 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 1 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 2 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 3 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 4 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 5 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 6 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 7 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 8 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 9 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 10 ef))
      (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEventAt 11 ef)))

private theorem DyadicMidpointChainTasteGate_single_carrier_alignment_round_trip
    (x : DyadicMidpointChainUp) :
    dyadicMidpointChainFromEventFlow (dyadicMidpointChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L R Q B O W A E H C P N =>
      change
        some
          (DyadicMidpointChainUp.mk
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist L))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist R))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist Q))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist B))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist O))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist W))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist A))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist E))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist H))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist C))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist P))
            (dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist N))) =
          some (DyadicMidpointChainUp.mk L R Q B O W A E H C P N)
      rw [DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode L,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode R,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode Q,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode B,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode O,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode W,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode A,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode E,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode H,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode C,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode P,
        DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicMidpointChainTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicMidpointChainUp} :
    dyadicMidpointChainToEventFlow x = dyadicMidpointChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicMidpointChainFromEventFlow (dyadicMidpointChainToEventFlow x) =
        dyadicMidpointChainFromEventFlow (dyadicMidpointChainToEventFlow y) :=
    congrArg dyadicMidpointChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicMidpointChainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicMidpointChainTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicMidpointChainBHistCarrier : BHistCarrier DyadicMidpointChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicMidpointChainToEventFlow
  fromEventFlow := dyadicMidpointChainFromEventFlow

instance dyadicMidpointChainChapterTasteGate :
    ChapterTasteGate DyadicMidpointChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicMidpointChainFromEventFlow (dyadicMidpointChainToEventFlow x) = some x
    exact DyadicMidpointChainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicMidpointChainTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicMidpointChainTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier DyadicMidpointChainUp,
        Nonempty (@ChapterTasteGate DyadicMidpointChainUp carrier)) ∧
      (∀ h : BHist,
        dyadicMidpointChainDecodeBHist (dyadicMidpointChainEncodeBHist h) = h) ∧
        (∀ x : DyadicMidpointChainUp,
          dyadicMidpointChainFromEventFlow (dyadicMidpointChainToEventFlow x) = some x) ∧
          dyadicMidpointChainEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨dyadicMidpointChainBHistCarrier,
        ⟨dyadicMidpointChainChapterTasteGate⟩⟩,
      DyadicMidpointChainTasteGate_single_carrier_alignment_decode_encode,
      DyadicMidpointChainTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.DyadicMidpointChainUp.TasteGate
