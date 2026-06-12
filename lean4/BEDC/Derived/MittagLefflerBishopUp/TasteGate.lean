import BEDC.Derived.MittagLefflerBishopUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MittagLefflerBishopUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def mittagLefflerBishopEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mittagLefflerBishopEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mittagLefflerBishopEncodeBHist h

def mittagLefflerBishopDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mittagLefflerBishopDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mittagLefflerBishopDecodeBHist tail)

private theorem MittagLefflerBishopTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mittagLefflerBishopFields : MittagLefflerBishopUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MittagLefflerBishopUp.mk interval window mesh stream readback realSeal transport replay
      provenance name =>
      [interval, window, mesh, stream, readback, realSeal, transport, replay, provenance, name]

def mittagLefflerBishopToEventFlow : MittagLefflerBishopUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (mittagLefflerBishopFields x).map mittagLefflerBishopEncodeBHist

private def mittagLefflerBishopEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mittagLefflerBishopEventAtDefault index rest

def mittagLefflerBishopFromEventFlow : EventFlow → Option MittagLefflerBishopUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MittagLefflerBishopUp.mk
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 0 ef))
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 1 ef))
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 2 ef))
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 3 ef))
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 4 ef))
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 5 ef))
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 6 ef))
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 7 ef))
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 8 ef))
        (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEventAtDefault 9 ef)))

private theorem MittagLefflerBishopTasteGate_single_carrier_alignment_round_trip
    (x : MittagLefflerBishopUp) :
    mittagLefflerBishopFromEventFlow (mittagLefflerBishopToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk interval window mesh stream readback realSeal transport replay provenance name =>
      change
        some
            (MittagLefflerBishopUp.mk
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist interval))
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist window))
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist mesh))
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist stream))
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist readback))
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist realSeal))
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist transport))
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist replay))
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist provenance))
              (mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist name))) =
          some
            (MittagLefflerBishopUp.mk interval window mesh stream readback realSeal
              transport replay provenance name)
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode interval]
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode window]
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode mesh]
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode stream]
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode readback]
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode realSeal]
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode transport]
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode replay]
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode provenance]
      rw [MittagLefflerBishopTasteGate_single_carrier_alignment_decode name]

private theorem MittagLefflerBishopTasteGate_single_carrier_alignment_injective
    {x y : MittagLefflerBishopUp} :
    mittagLefflerBishopToEventFlow x = mittagLefflerBishopToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mittagLefflerBishopFromEventFlow (mittagLefflerBishopToEventFlow x) =
        mittagLefflerBishopFromEventFlow (mittagLefflerBishopToEventFlow y) :=
    congrArg mittagLefflerBishopFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MittagLefflerBishopTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MittagLefflerBishopTasteGate_single_carrier_alignment_round_trip y)))

instance mittagLefflerBishopBHistCarrier : BHistCarrier MittagLefflerBishopUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mittagLefflerBishopToEventFlow
  fromEventFlow := mittagLefflerBishopFromEventFlow

instance mittagLefflerBishopChapterTasteGate : ChapterTasteGate MittagLefflerBishopUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mittagLefflerBishopFromEventFlow (mittagLefflerBishopToEventFlow x) = some x
    exact MittagLefflerBishopTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MittagLefflerBishopTasteGate_single_carrier_alignment_injective heq)

theorem MittagLefflerBishopTasteGate_single_carrier_alignment :
    (∀ h : BHist, mittagLefflerBishopDecodeBHist (mittagLefflerBishopEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MittagLefflerBishopUp) ∧
        Nonempty (ChapterTasteGate MittagLefflerBishopUp) ∧
          mittagLefflerBishopEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MittagLefflerBishopTasteGate_single_carrier_alignment_decode,
      ⟨⟨mittagLefflerBishopBHistCarrier⟩,
        ⟨⟨mittagLefflerBishopChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.MittagLefflerBishopUp
