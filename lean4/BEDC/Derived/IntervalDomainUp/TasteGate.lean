import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalDomainUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalDomainUp : Type where
  | mk (L R N W Q E H C P A : BHist) : IntervalDomainUp
  deriving DecidableEq

def intervalDomainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalDomainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalDomainEncodeBHist h

def intervalDomainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalDomainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalDomainDecodeBHist tail)

private theorem IntervalDomainTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, intervalDomainDecodeBHist (intervalDomainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalDomainFields : IntervalDomainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalDomainUp.mk L R N W Q E H C P A => [L, R, N, W, Q, E, H, C, P, A]

def intervalDomainToEventFlow : IntervalDomainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (intervalDomainFields x).map intervalDomainEncodeBHist

private def intervalDomainEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => intervalDomainEventAt index rest

def intervalDomainFromEventFlow (ef : EventFlow) : Option IntervalDomainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalDomainUp.mk
      (intervalDomainDecodeBHist (intervalDomainEventAt 0 ef))
      (intervalDomainDecodeBHist (intervalDomainEventAt 1 ef))
      (intervalDomainDecodeBHist (intervalDomainEventAt 2 ef))
      (intervalDomainDecodeBHist (intervalDomainEventAt 3 ef))
      (intervalDomainDecodeBHist (intervalDomainEventAt 4 ef))
      (intervalDomainDecodeBHist (intervalDomainEventAt 5 ef))
      (intervalDomainDecodeBHist (intervalDomainEventAt 6 ef))
      (intervalDomainDecodeBHist (intervalDomainEventAt 7 ef))
      (intervalDomainDecodeBHist (intervalDomainEventAt 8 ef))
      (intervalDomainDecodeBHist (intervalDomainEventAt 9 ef)))

private theorem IntervalDomainTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IntervalDomainUp,
      intervalDomainFromEventFlow (intervalDomainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R N W Q E H C P A =>
      change
        some
          (IntervalDomainUp.mk
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist L))
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist R))
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist N))
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist W))
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist Q))
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist E))
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist H))
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist C))
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist P))
            (intervalDomainDecodeBHist (intervalDomainEncodeBHist A))) =
          some (IntervalDomainUp.mk L R N W Q E H C P A)
      rw [IntervalDomainTasteGate_single_carrier_alignment_decode_encode L,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode R,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode N,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode W,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode Q,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode E,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode H,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode C,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode P,
        IntervalDomainTasteGate_single_carrier_alignment_decode_encode A]

private theorem IntervalDomainTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IntervalDomainUp} :
    intervalDomainToEventFlow x = intervalDomainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalDomainFromEventFlow (intervalDomainToEventFlow x) =
        intervalDomainFromEventFlow (intervalDomainToEventFlow y) :=
    congrArg intervalDomainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IntervalDomainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IntervalDomainTasteGate_single_carrier_alignment_round_trip y)))

instance intervalDomainBHistCarrier : BHistCarrier IntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalDomainToEventFlow
  fromEventFlow := intervalDomainFromEventFlow

local instance intervalDomainChapterTasteGate : ChapterTasteGate IntervalDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change intervalDomainFromEventFlow (intervalDomainToEventFlow x) = some x
    exact IntervalDomainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntervalDomainTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem IntervalDomainTasteGate_single_carrier_alignment :
    (∀ h : BHist, intervalDomainDecodeBHist (intervalDomainEncodeBHist h) = h) ∧
      (∀ x : IntervalDomainUp,
        intervalDomainFromEventFlow (intervalDomainToEventFlow x) = some x) ∧
        (∀ x y : IntervalDomainUp,
          intervalDomainToEventFlow x = intervalDomainToEventFlow y → x = y) ∧
          intervalDomainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨IntervalDomainTasteGate_single_carrier_alignment_decode_encode,
      IntervalDomainTasteGate_single_carrier_alignment_round_trip,
      (by
        intro x y heq
        exact IntervalDomainTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.IntervalDomainUp.TasteGate
