import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveLipschitzFlowUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveLipschitzFlowUp : Type where
  | mk (M T L E W H C P N : BHist) : ConstructiveLipschitzFlowUp
  deriving DecidableEq

def constructiveLipschitzFlowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveLipschitzFlowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveLipschitzFlowEncodeBHist h

def constructiveLipschitzFlowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveLipschitzFlowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveLipschitzFlowDecodeBHist tail)

private theorem ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveLipschitzFlowFields : ConstructiveLipschitzFlowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveLipschitzFlowUp.mk M T L E W H C P N => [M, T, L, E, W, H, C, P, N]

def constructiveLipschitzFlowToEventFlow : ConstructiveLipschitzFlowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (constructiveLipschitzFlowFields x).map constructiveLipschitzFlowEncodeBHist

private def ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt index rest

def constructiveLipschitzFlowDecodeFields (ef : EventFlow) : ConstructiveLipschitzFlowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ConstructiveLipschitzFlowUp.mk
    (constructiveLipschitzFlowDecodeBHist
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt 0 ef))
    (constructiveLipschitzFlowDecodeBHist
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt 1 ef))
    (constructiveLipschitzFlowDecodeBHist
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt 2 ef))
    (constructiveLipschitzFlowDecodeBHist
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt 3 ef))
    (constructiveLipschitzFlowDecodeBHist
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt 4 ef))
    (constructiveLipschitzFlowDecodeBHist
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt 5 ef))
    (constructiveLipschitzFlowDecodeBHist
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt 6 ef))
    (constructiveLipschitzFlowDecodeBHist
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt 7 ef))
    (constructiveLipschitzFlowDecodeBHist
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_eventAt 8 ef))

def constructiveLipschitzFlowFromEventFlow
    (ef : EventFlow) : Option ConstructiveLipschitzFlowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (constructiveLipschitzFlowDecodeFields ef)

private theorem ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveLipschitzFlowUp) :
    constructiveLipschitzFlowFromEventFlow (constructiveLipschitzFlowToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M T L E W H C P N =>
      change
        some
          (ConstructiveLipschitzFlowUp.mk
            (constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist M))
            (constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist T))
            (constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist L))
            (constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist E))
            (constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist W))
            (constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist H))
            (constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist C))
            (constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist P))
            (constructiveLipschitzFlowDecodeBHist (constructiveLipschitzFlowEncodeBHist N))) =
          some (ConstructiveLipschitzFlowUp.mk M T L E W H C P N)
      rw [ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode M,
        ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode T,
        ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode L,
        ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode E,
        ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode W,
        ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveLipschitzFlowUp} :
    constructiveLipschitzFlowToEventFlow x = constructiveLipschitzFlowToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveLipschitzFlowFromEventFlow (constructiveLipschitzFlowToEventFlow x) =
        constructiveLipschitzFlowFromEventFlow (constructiveLipschitzFlowToEventFlow y) :=
    congrArg constructiveLipschitzFlowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveLipschitzFlowBHistCarrier :
    BHistCarrier ConstructiveLipschitzFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveLipschitzFlowToEventFlow
  fromEventFlow := constructiveLipschitzFlowFromEventFlow

instance constructiveLipschitzFlowChapterTasteGate :
    ChapterTasteGate ConstructiveLipschitzFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveLipschitzFlowFromEventFlow (constructiveLipschitzFlowToEventFlow x) =
      some x
    exact ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ConstructiveLipschitzFlowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveLipschitzFlowChapterTasteGate

theorem ConstructiveLipschitzFlowTasteGate_single_carrier_alignment :
    (∀ h : BHist, constructiveLipschitzFlowDecodeBHist
      (constructiveLipschitzFlowEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ConstructiveLipschitzFlowUp) ∧
        Nonempty (ChapterTasteGate ConstructiveLipschitzFlowUp) ∧
          constructiveLipschitzFlowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConstructiveLipschitzFlowTasteGate_single_carrier_alignment_decode_encode,
      ⟨constructiveLipschitzFlowBHistCarrier⟩,
      ⟨constructiveLipschitzFlowChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ConstructiveLipschitzFlowUp.TasteGate
