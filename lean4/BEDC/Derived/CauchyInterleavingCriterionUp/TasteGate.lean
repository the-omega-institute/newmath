import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyInterleavingCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyInterleavingCriterionUp : Type where
  | mk (sourceLeft sourceRight ledgerLeft ledgerRight selector extractedWindow readback realSeal
      transport replay provenance localName : BHist) : CauchyInterleavingCriterionUp
  deriving DecidableEq

def cauchyInterleavingCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyInterleavingCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyInterleavingCriterionEncodeBHist h

def cauchyInterleavingCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyInterleavingCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyInterleavingCriterionDecodeBHist tail)

private theorem CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyInterleavingCriterionFields :
    CauchyInterleavingCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyInterleavingCriterionUp.mk sourceLeft sourceRight ledgerLeft ledgerRight selector
      extractedWindow readback realSeal transport replay provenance localName =>
      [sourceLeft, sourceRight, ledgerLeft, ledgerRight, selector, extractedWindow, readback,
        realSeal, transport, replay, provenance, localName]

def cauchyInterleavingCriterionToEventFlow :
    CauchyInterleavingCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyInterleavingCriterionFields x).map cauchyInterleavingCriterionEncodeBHist

private def cauchyInterleavingCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyInterleavingCriterionEventAt index rest

def cauchyInterleavingCriterionFromEventFlow (ef : EventFlow) :
    Option CauchyInterleavingCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyInterleavingCriterionUp.mk
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 0 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 1 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 2 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 3 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 4 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 5 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 6 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 7 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 8 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 9 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 10 ef))
      (cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEventAt 11 ef)))

def cauchyInterleavingCriterionBHistCarrier :
    BHistCarrier CauchyInterleavingCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyInterleavingCriterionToEventFlow
  fromEventFlow := cauchyInterleavingCriterionFromEventFlow

instance cauchyInterleavingCriterionBHistCarrierInstance :
    BHistCarrier CauchyInterleavingCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyInterleavingCriterionBHistCarrier

private theorem CauchyInterleavingCriterionTasteGate_single_carrier_alignment_round_trip
    (x : CauchyInterleavingCriterionUp) :
    cauchyInterleavingCriterionFromEventFlow (cauchyInterleavingCriterionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk sourceLeft sourceRight ledgerLeft ledgerRight selector extractedWindow readback realSeal
      transport replay provenance localName =>
      change
        some
          (CauchyInterleavingCriterionUp.mk
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist sourceLeft))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist sourceRight))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist ledgerLeft))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist ledgerRight))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist selector))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist extractedWindow))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist readback))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist realSeal))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist transport))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist replay))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist provenance))
            (cauchyInterleavingCriterionDecodeBHist
              (cauchyInterleavingCriterionEncodeBHist localName))) =
          some
            (CauchyInterleavingCriterionUp.mk sourceLeft sourceRight ledgerLeft ledgerRight
              selector extractedWindow readback realSeal transport replay provenance localName)
      rw [CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode sourceLeft,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode sourceRight,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode ledgerLeft,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode ledgerRight,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode selector,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode
          extractedWindow,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode readback,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode realSeal,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CauchyInterleavingCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyInterleavingCriterionUp} :
    cauchyInterleavingCriterionToEventFlow x = cauchyInterleavingCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyInterleavingCriterionFromEventFlow (cauchyInterleavingCriterionToEventFlow x) =
        cauchyInterleavingCriterionFromEventFlow (cauchyInterleavingCriterionToEventFlow y) :=
    congrArg cauchyInterleavingCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyInterleavingCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyInterleavingCriterionTasteGate_single_carrier_alignment_round_trip y)))

def cauchyInterleavingCriterionChapterTasteGate :
    @ChapterTasteGate CauchyInterleavingCriterionUp cauchyInterleavingCriterionBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact CauchyInterleavingCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyInterleavingCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyInterleavingCriterionChapterTasteGateInstance :
    ChapterTasteGate CauchyInterleavingCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyInterleavingCriterionChapterTasteGate

theorem CauchyInterleavingCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyInterleavingCriterionDecodeBHist (cauchyInterleavingCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyInterleavingCriterionUp) ∧
      Nonempty (ChapterTasteGate CauchyInterleavingCriterionUp) ∧
      cauchyInterleavingCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyInterleavingCriterionTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨cauchyInterleavingCriterionBHistCarrier⟩,
        ⟨⟨cauchyInterleavingCriterionChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.CauchyInterleavingCriterionUp
