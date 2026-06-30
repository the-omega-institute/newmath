import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedCauchyFilterUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedCauchyFilterUp : Type where
  | mk
      (source boundedFace dyadic windows readback realSeal transport replay provenance
        localName : BHist) :
      BoundedCauchyFilterUp
  deriving DecidableEq

def boundedCauchyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedCauchyFilterEncodeBHist h

def boundedCauchyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedCauchyFilterDecodeBHist tail)

private theorem BoundedCauchyFilterUp_decode_encode :
    ∀ h : BHist, boundedCauchyFilterDecodeBHist
      (boundedCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedCauchyFilterFields : BoundedCauchyFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedCauchyFilterUp.mk source boundedFace dyadic windows readback realSeal transport
      replay provenance localName =>
      [source, boundedFace, dyadic, windows, readback, realSeal, transport, replay,
        provenance, localName]

def boundedCauchyFilterToEventFlow : BoundedCauchyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedCauchyFilterFields x).map boundedCauchyFilterEncodeBHist

private def boundedCauchyFilterEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedCauchyFilterEventAt index rest

def boundedCauchyFilterFromEventFlow (ef : EventFlow) :
    Option BoundedCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedCauchyFilterUp.mk
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 0 ef))
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 1 ef))
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 2 ef))
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 3 ef))
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 4 ef))
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 5 ef))
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 6 ef))
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 7 ef))
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 8 ef))
      (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEventAt 9 ef)))

private theorem BoundedCauchyFilterUp_round_trip
    (x : BoundedCauchyFilterUp) :
    boundedCauchyFilterFromEventFlow (boundedCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source boundedFace dyadic windows readback realSeal transport replay provenance
      localName =>
      change
        some
          (BoundedCauchyFilterUp.mk
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist source))
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist boundedFace))
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist dyadic))
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist windows))
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist readback))
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist realSeal))
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist transport))
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist replay))
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist provenance))
            (boundedCauchyFilterDecodeBHist (boundedCauchyFilterEncodeBHist localName))) =
          some
            (BoundedCauchyFilterUp.mk source boundedFace dyadic windows readback realSeal
              transport replay provenance localName)
      rw [BoundedCauchyFilterUp_decode_encode source,
        BoundedCauchyFilterUp_decode_encode boundedFace,
        BoundedCauchyFilterUp_decode_encode dyadic,
        BoundedCauchyFilterUp_decode_encode windows,
        BoundedCauchyFilterUp_decode_encode readback,
        BoundedCauchyFilterUp_decode_encode realSeal,
        BoundedCauchyFilterUp_decode_encode transport,
        BoundedCauchyFilterUp_decode_encode replay,
        BoundedCauchyFilterUp_decode_encode provenance,
        BoundedCauchyFilterUp_decode_encode localName]

private theorem boundedCauchyFilterToEventFlow_injective {x y : BoundedCauchyFilterUp} :
    boundedCauchyFilterToEventFlow x = boundedCauchyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedCauchyFilterFromEventFlow (boundedCauchyFilterToEventFlow x) =
        boundedCauchyFilterFromEventFlow (boundedCauchyFilterToEventFlow y) :=
    congrArg boundedCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedCauchyFilterUp_round_trip x).symm
      (Eq.trans hread (BoundedCauchyFilterUp_round_trip y)))

private theorem boundedCauchyFilter_fields_faithful :
    ∀ x y : BoundedCauchyFilterUp,
      boundedCauchyFilterFields x = boundedCauchyFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source1 boundedFace1 dyadic1 windows1 readback1 realSeal1 transport1 replay1
      provenance1 localName1 =>
      cases y with
      | mk source2 boundedFace2 dyadic2 windows2 readback2 realSeal2 transport2 replay2
          provenance2 localName2 =>
          cases hfields
          rfl

instance boundedCauchyFilterBHistCarrier : BHistCarrier BoundedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedCauchyFilterToEventFlow
  fromEventFlow := boundedCauchyFilterFromEventFlow

instance boundedCauchyFilterChapterTasteGate :
    ChapterTasteGate BoundedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedCauchyFilterFromEventFlow (boundedCauchyFilterToEventFlow x) = some x
    exact BoundedCauchyFilterUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedCauchyFilterToEventFlow_injective heq)

instance boundedCauchyFilterFieldFaithful : FieldFaithful BoundedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedCauchyFilterFields
  field_faithful := boundedCauchyFilter_fields_faithful

instance boundedCauchyFilterNontrivial : Nontrivial BoundedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedCauchyFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedCauchyFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedCauchyFilterChapterTasteGate

theorem BoundedCauchyFilterTasteGate_single_carrier_alignment :
    (∀ x : BoundedCauchyFilterUp,
      boundedCauchyFilterFromEventFlow (boundedCauchyFilterToEventFlow x) = some x) ∧
      (∀ x y : BoundedCauchyFilterUp,
        boundedCauchyFilterToEventFlow x = boundedCauchyFilterToEventFlow y → x = y) ∧
      boundedCauchyFilterFields
          (BoundedCauchyFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨BoundedCauchyFilterUp_round_trip,
      (fun _ _ heq => boundedCauchyFilterToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedCauchyFilterUp.TasteGate
