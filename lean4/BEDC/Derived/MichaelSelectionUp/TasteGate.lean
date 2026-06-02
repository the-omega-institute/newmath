import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MichaelSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MichaelSelectionUp : Type where
  | mk (D V K L S F H C P N : BHist) : MichaelSelectionUp
  deriving DecidableEq

def michaelSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: michaelSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: michaelSelectionEncodeBHist h

def michaelSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (michaelSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (michaelSelectionDecodeBHist tail)

private theorem MichaelSelectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, michaelSelectionDecodeBHist (michaelSelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def michaelSelectionFields : MichaelSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MichaelSelectionUp.mk D V K L S F H C P N => [D, V, K, L, S, F, H, C, P, N]

def michaelSelectionToEventFlow : MichaelSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (michaelSelectionFields x).map michaelSelectionEncodeBHist

private def MichaelSelectionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      MichaelSelectionTasteGate_single_carrier_alignment_eventAt index rest

def michaelSelectionFromEventFlow (ef : EventFlow) : Option MichaelSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MichaelSelectionUp.mk
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 0 ef))
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 1 ef))
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 2 ef))
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 3 ef))
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 4 ef))
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 5 ef))
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 6 ef))
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 7 ef))
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 8 ef))
      (michaelSelectionDecodeBHist
        (MichaelSelectionTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem MichaelSelectionTasteGate_single_carrier_alignment_round_trip
    (x : MichaelSelectionUp) :
    michaelSelectionFromEventFlow (michaelSelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D V K L S F H C P N =>
      change
        some
          (MichaelSelectionUp.mk
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist D))
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist V))
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist K))
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist L))
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist S))
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist F))
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist H))
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist C))
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist P))
            (michaelSelectionDecodeBHist (michaelSelectionEncodeBHist N))) =
          some (MichaelSelectionUp.mk D V K L S F H C P N)
      rw [MichaelSelectionTasteGate_single_carrier_alignment_decode_encode D,
        MichaelSelectionTasteGate_single_carrier_alignment_decode_encode V,
        MichaelSelectionTasteGate_single_carrier_alignment_decode_encode K,
        MichaelSelectionTasteGate_single_carrier_alignment_decode_encode L,
        MichaelSelectionTasteGate_single_carrier_alignment_decode_encode S,
        MichaelSelectionTasteGate_single_carrier_alignment_decode_encode F,
        MichaelSelectionTasteGate_single_carrier_alignment_decode_encode H,
        MichaelSelectionTasteGate_single_carrier_alignment_decode_encode C,
        MichaelSelectionTasteGate_single_carrier_alignment_decode_encode P,
        MichaelSelectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem MichaelSelectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MichaelSelectionUp} :
    michaelSelectionToEventFlow x = michaelSelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      michaelSelectionFromEventFlow (michaelSelectionToEventFlow x) =
        michaelSelectionFromEventFlow (michaelSelectionToEventFlow y) :=
    congrArg michaelSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MichaelSelectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MichaelSelectionTasteGate_single_carrier_alignment_round_trip y)))

instance michaelSelectionBHistCarrier : BHistCarrier MichaelSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := michaelSelectionToEventFlow
  fromEventFlow := michaelSelectionFromEventFlow

instance michaelSelectionChapterTasteGate : ChapterTasteGate MichaelSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change michaelSelectionFromEventFlow (michaelSelectionToEventFlow x) = some x
    exact MichaelSelectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MichaelSelectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MichaelSelectionTasteGate_single_carrier_alignment :
    (michaelSelectionEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (michaelSelectionDecodeBHist [BMark.b0] = BHist.e0 BHist.Empty) ∧
        (∀ h : BHist, michaelSelectionDecodeBHist (michaelSelectionEncodeBHist h) = h) ∧
          Nonempty (BHistCarrier MichaelSelectionUp) ∧
            Nonempty (ChapterTasteGate MichaelSelectionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, rfl, MichaelSelectionTasteGate_single_carrier_alignment_decode_encode,
      ⟨michaelSelectionBHistCarrier⟩, ⟨michaelSelectionChapterTasteGate⟩⟩

end BEDC.Derived.MichaelSelectionUp
