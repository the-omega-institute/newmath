import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySubnetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySubnetUp : Type where
  | mk
      (filter subnet window readback tolerance limit sealRow transport replay provenance
        localName : BHist) :
      CauchySubnetUp
  deriving DecidableEq

def cauchySubnetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySubnetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySubnetEncodeBHist h

def cauchySubnetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySubnetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySubnetDecodeBHist tail)

private theorem CauchySubnetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchySubnetDecodeBHist (cauchySubnetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySubnetFields : CauchySubnetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySubnetUp.mk filter subnet window readback tolerance limit sealRow transport replay
      provenance localName =>
      [filter, subnet, window, readback, tolerance, limit, sealRow, transport, replay,
        provenance, localName]

def cauchySubnetToEventFlow : CauchySubnetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySubnetFields x).map cauchySubnetEncodeBHist

private def cauchySubnetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySubnetEventAt index rest

def cauchySubnetFromEventFlow : EventFlow → Option CauchySubnetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    some
      (CauchySubnetUp.mk
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 0 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 1 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 2 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 3 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 4 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 5 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 6 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 7 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 8 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 9 eventFlow))
        (cauchySubnetDecodeBHist (cauchySubnetEventAt 10 eventFlow)))

private theorem CauchySubnetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchySubnetUp,
      cauchySubnetFromEventFlow (cauchySubnetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk filter subnet window readback tolerance limit sealRow transport replay provenance
      localName =>
      change
        some
            (CauchySubnetUp.mk
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist filter))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist subnet))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist window))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist readback))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist tolerance))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist limit))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist sealRow))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist transport))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist replay))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist provenance))
              (cauchySubnetDecodeBHist (cauchySubnetEncodeBHist localName))) =
          some
            (CauchySubnetUp.mk filter subnet window readback tolerance limit sealRow
              transport replay provenance localName)
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode filter]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode subnet]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode window]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode readback]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode tolerance]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode limit]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode sealRow]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode transport]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode replay]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [CauchySubnetTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CauchySubnetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySubnetUp} :
    cauchySubnetToEventFlow x = cauchySubnetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySubnetFromEventFlow (cauchySubnetToEventFlow x) =
        cauchySubnetFromEventFlow (cauchySubnetToEventFlow y) :=
    congrArg cauchySubnetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySubnetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchySubnetTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySubnetBHistCarrier : BHistCarrier CauchySubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySubnetToEventFlow
  fromEventFlow := cauchySubnetFromEventFlow

instance cauchySubnetChapterTasteGate : ChapterTasteGate CauchySubnetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySubnetFromEventFlow (cauchySubnetToEventFlow x) = some x
    exact CauchySubnetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySubnetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchySubnetTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchySubnetDecodeBHist (cauchySubnetEncodeBHist h) = h) ∧
      (∀ x : CauchySubnetUp, cauchySubnetFromEventFlow (cauchySubnetToEventFlow x) = some x) ∧
      Nonempty (BHistCarrier CauchySubnetUp) ∧ Nonempty (ChapterTasteGate CauchySubnetUp) ∧
        cauchySubnetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchySubnetTasteGate_single_carrier_alignment_decode_encode,
      CauchySubnetTasteGate_single_carrier_alignment_round_trip,
      ⟨cauchySubnetBHistCarrier⟩, ⟨cauchySubnetChapterTasteGate⟩, rfl⟩

end BEDC.Derived.CauchySubnetUp
