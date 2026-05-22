import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ToeplitzLemmaUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ToeplitzLemmaUp : Type where
  | mk (matrixWindow sourceWindow readback dyadicLedger transformedRow realSeal transport
      continuation provenance name : BHist) : ToeplitzLemmaUp
  deriving DecidableEq

def toeplitzLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: toeplitzLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: toeplitzLemmaEncodeBHist h

def toeplitzLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (toeplitzLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (toeplitzLemmaDecodeBHist tail)

private theorem toeplitzLemmaDecode_encode_bhist :
    ∀ h : BHist, toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def toeplitzLemmaFields : ToeplitzLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ToeplitzLemmaUp.mk matrixWindow sourceWindow readback dyadicLedger transformedRow
      realSeal transport continuation provenance name =>
      [matrixWindow, sourceWindow, readback, dyadicLedger, transformedRow, realSeal,
        transport, continuation, provenance, name]

def toeplitzLemmaToEventFlow : ToeplitzLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (toeplitzLemmaFields x).map toeplitzLemmaEncodeBHist

def toeplitzLemmaFromEventFlow : EventFlow → Option ToeplitzLemmaUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | matrixWindow :: sourceWindow :: readback :: dyadicLedger :: transformedRow ::
      realSeal :: transport :: continuation :: provenance :: name :: [] =>
      some
        (ToeplitzLemmaUp.mk
          (toeplitzLemmaDecodeBHist matrixWindow)
          (toeplitzLemmaDecodeBHist sourceWindow)
          (toeplitzLemmaDecodeBHist readback)
          (toeplitzLemmaDecodeBHist dyadicLedger)
          (toeplitzLemmaDecodeBHist transformedRow)
          (toeplitzLemmaDecodeBHist realSeal)
          (toeplitzLemmaDecodeBHist transport)
          (toeplitzLemmaDecodeBHist continuation)
          (toeplitzLemmaDecodeBHist provenance)
          (toeplitzLemmaDecodeBHist name))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k ::
      _rest => none

private theorem toeplitzLemma_round_trip :
    ∀ x : ToeplitzLemmaUp,
      toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk matrixWindow sourceWindow readback dyadicLedger transformedRow realSeal transport
      continuation provenance name =>
      change
        some
          (ToeplitzLemmaUp.mk
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist matrixWindow))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist sourceWindow))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist readback))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist dyadicLedger))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist transformedRow))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist realSeal))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist transport))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist continuation))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist provenance))
            (toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist name))) =
          some
            (ToeplitzLemmaUp.mk matrixWindow sourceWindow readback dyadicLedger
              transformedRow realSeal transport continuation provenance name)
      rw [toeplitzLemmaDecode_encode_bhist matrixWindow,
        toeplitzLemmaDecode_encode_bhist sourceWindow,
        toeplitzLemmaDecode_encode_bhist readback,
        toeplitzLemmaDecode_encode_bhist dyadicLedger,
        toeplitzLemmaDecode_encode_bhist transformedRow,
        toeplitzLemmaDecode_encode_bhist realSeal,
        toeplitzLemmaDecode_encode_bhist transport,
        toeplitzLemmaDecode_encode_bhist continuation,
        toeplitzLemmaDecode_encode_bhist provenance,
        toeplitzLemmaDecode_encode_bhist name]

private theorem toeplitzLemmaToEventFlow_injective {x y : ToeplitzLemmaUp} :
    toeplitzLemmaToEventFlow x = toeplitzLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow x) =
        toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow y) :=
    congrArg toeplitzLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (toeplitzLemma_round_trip x).symm
      (Eq.trans hread (toeplitzLemma_round_trip y)))

private theorem toeplitzLemma_fields_faithful :
    ∀ x y : ToeplitzLemmaUp, toeplitzLemmaFields x = toeplitzLemmaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk matrixWindow sourceWindow readback dyadicLedger transformedRow realSeal transport
      continuation provenance name =>
      cases y with
      | mk matrixWindow' sourceWindow' readback' dyadicLedger' transformedRow' realSeal'
          transport' continuation' provenance' name' =>
          cases hfields
          rfl

instance toeplitzLemmaBHistCarrier : BHistCarrier ToeplitzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := toeplitzLemmaToEventFlow
  fromEventFlow := toeplitzLemmaFromEventFlow

instance toeplitzLemmaChapterTasteGate : ChapterTasteGate ToeplitzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow x) = some x
    exact toeplitzLemma_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (toeplitzLemmaToEventFlow_injective heq)

instance toeplitzLemmaFieldFaithful : FieldFaithful ToeplitzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := toeplitzLemmaFields
  field_faithful := toeplitzLemma_fields_faithful

instance toeplitzLemmaNontrivial : Nontrivial ToeplitzLemmaUp where
  witness_pair :=
    ⟨ToeplitzLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ToeplitzLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ToeplitzLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  toeplitzLemmaChapterTasteGate

theorem ToeplitzLemmaTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ToeplitzLemmaUp) ∧
      Nonempty (FieldFaithful ToeplitzLemmaUp) ∧
      Nonempty (Nontrivial ToeplitzLemmaUp) ∧
      (∀ h : BHist, toeplitzLemmaDecodeBHist (toeplitzLemmaEncodeBHist h) = h) ∧
      (∀ x : ToeplitzLemmaUp,
        toeplitzLemmaFromEventFlow (toeplitzLemmaToEventFlow x) = some x) ∧
      (∀ x y : ToeplitzLemmaUp,
        toeplitzLemmaToEventFlow x = toeplitzLemmaToEventFlow y → x = y) ∧
      toeplitzLemmaEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨⟨toeplitzLemmaChapterTasteGate⟩, ⟨toeplitzLemmaFieldFaithful⟩,
    ⟨toeplitzLemmaNontrivial⟩, toeplitzLemmaDecode_encode_bhist,
    toeplitzLemma_round_trip, fun _ _ heq => toeplitzLemmaToEventFlow_injective heq, rfl⟩

end BEDC.Derived.ToeplitzLemmaUp.TasteGate
