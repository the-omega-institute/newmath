import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSimplicialChainUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSimplicialChainUp : Type where
  | mk (K F A G B Z H T P N : BHist) : FiniteSimplicialChainUp
  deriving DecidableEq

def finiteSimplicialChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSimplicialChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSimplicialChainEncodeBHist h

def finiteSimplicialChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSimplicialChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSimplicialChainDecodeBHist tail)

private theorem FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteSimplicialChainFields : FiniteSimplicialChainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSimplicialChainUp.mk K F A G B Z H T P N => [K, F, A, G, B, Z, H, T, P, N]

def finiteSimplicialChainToEventFlow : FiniteSimplicialChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteSimplicialChainFields x).map finiteSimplicialChainEncodeBHist

private def finiteSimplicialChainEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteSimplicialChainEventAt index rest

def finiteSimplicialChainFromEventFlow (ef : EventFlow) : Option FiniteSimplicialChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteSimplicialChainUp.mk
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 0 ef))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 1 ef))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 2 ef))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 3 ef))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 4 ef))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 5 ef))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 6 ef))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 7 ef))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 8 ef))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 9 ef)))

private theorem FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip
    (x : FiniteSimplicialChainUp) :
    finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F A G B Z H T P N =>
      change
        some
          (FiniteSimplicialChainUp.mk
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist K))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist F))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist A))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist G))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist B))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist Z))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist H))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist T))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist P))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist N))) =
          some (FiniteSimplicialChainUp.mk K F A G B Z H T P N)
      rw [FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode K,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode F,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode A,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode G,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode B,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode Z,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode H,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode T,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode P,
        FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteSimplicialChainTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteSimplicialChainUp} :
    finiteSimplicialChainToEventFlow x = finiteSimplicialChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) =
        finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow y) :=
    congrArg finiteSimplicialChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip y)))

instance finiteSimplicialChainBHistCarrier : BHistCarrier FiniteSimplicialChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSimplicialChainToEventFlow
  fromEventFlow := finiteSimplicialChainFromEventFlow

instance finiteSimplicialChainChapterTasteGate : ChapterTasteGate FiniteSimplicialChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) = some x
    exact FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteSimplicialChainTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def FiniteSimplicialChainTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FiniteSimplicialChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteSimplicialChainChapterTasteGate

theorem FiniteSimplicialChainTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist h) = h) ∧
      (∀ x : FiniteSimplicialChainUp,
        finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) = some x) ∧
        (∀ x y : FiniteSimplicialChainUp,
          finiteSimplicialChainToEventFlow x = finiteSimplicialChainToEventFlow y → x = y) ∧
          finiteSimplicialChainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteSimplicialChainTasteGate_single_carrier_alignment_decode_encode,
      FiniteSimplicialChainTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteSimplicialChainTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteSimplicialChainUp.TasteGate
