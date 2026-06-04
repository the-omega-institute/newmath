import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetrizableSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetrizableSpaceUp : Type where
  | mk
      (topology metric ball window readback sealRow transportRow replay provenance name : BHist) :
      MetrizableSpaceUp
  deriving DecidableEq

def metrizableSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metrizableSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metrizableSpaceEncodeBHist h

def metrizableSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metrizableSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metrizableSpaceDecodeBHist tail)

private theorem metrizableSpaceDecodeEncode :
    ∀ h : BHist, metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metrizableSpaceFields : MetrizableSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetrizableSpaceUp.mk topology metric ball window readback sealRow transportRow replay
      provenance name =>
      [topology, metric, ball, window, readback, sealRow, transportRow, replay, provenance, name]

def metrizableSpaceToEventFlow : MetrizableSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (metrizableSpaceFields x).map metrizableSpaceEncodeBHist

private def metrizableSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metrizableSpaceEventAtDefault index rest

def metrizableSpaceFromEventFlow (ef : EventFlow) : Option MetrizableSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetrizableSpaceUp.mk
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 0 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 1 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 2 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 3 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 4 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 5 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 6 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 7 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 8 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 9 ef)))

private theorem metrizableSpaceRoundTrip :
    ∀ x : MetrizableSpaceUp,
      metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk topology metric ball window readback sealRow transportRow replay provenance name =>
      change
        some
          (MetrizableSpaceUp.mk
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist topology))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist metric))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist ball))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist window))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist readback))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist sealRow))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist transportRow))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist replay))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist provenance))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist name))) =
          some
            (MetrizableSpaceUp.mk topology metric ball window readback sealRow transportRow replay
              provenance name)
      rw [metrizableSpaceDecodeEncode topology, metrizableSpaceDecodeEncode metric,
        metrizableSpaceDecodeEncode ball, metrizableSpaceDecodeEncode window,
        metrizableSpaceDecodeEncode readback, metrizableSpaceDecodeEncode sealRow,
        metrizableSpaceDecodeEncode transportRow, metrizableSpaceDecodeEncode replay,
        metrizableSpaceDecodeEncode provenance, metrizableSpaceDecodeEncode name]

private theorem metrizableSpaceToEventFlow_injective {x y : MetrizableSpaceUp} :
    metrizableSpaceToEventFlow x = metrizableSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow x) =
        metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow y) :=
    congrArg metrizableSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metrizableSpaceRoundTrip x).symm
      (Eq.trans hread (metrizableSpaceRoundTrip y)))

private theorem metrizableSpaceFieldFaithfulProof :
    ∀ x y : MetrizableSpaceUp, metrizableSpaceFields x = metrizableSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk topology₁ metric₁ ball₁ window₁ readback₁ seal₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
        | mk topology₂ metric₂ ball₂ window₂ readback₂ seal₂ transport₂ replay₂ provenance₂
          name₂ =>
          change
            [topology₁, metric₁, ball₁, window₁, readback₁, seal₁, transport₁, replay₁,
              provenance₁, name₁] =
              [topology₂, metric₂, ball₂, window₂, readback₂, seal₂, transport₂, replay₂,
                provenance₂, name₂] at h
          cases h
          rfl

instance metrizableSpaceBHistCarrier : BHistCarrier MetrizableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metrizableSpaceToEventFlow
  fromEventFlow := metrizableSpaceFromEventFlow

instance metrizableSpaceChapterTasteGate : ChapterTasteGate MetrizableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow x) = some x
    exact metrizableSpaceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metrizableSpaceToEventFlow_injective heq)

instance metrizableSpaceFieldFaithful : FieldFaithful MetrizableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metrizableSpaceFields
  field_faithful := metrizableSpaceFieldFaithfulProof

theorem MetrizableSpaceTasteGate_single_carrier_alignment :
    (∀ x : MetrizableSpaceUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
        ChapterTasteGate MetrizableSpaceUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · intro x
    change metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow x) = some x
    exact metrizableSpaceRoundTrip x
  · exact metrizableSpaceChapterTasteGate

end BEDC.Derived.MetrizableSpaceUp
