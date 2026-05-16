import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OpenFitResidueGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OpenFitResidueGateUp : Type where
  | mk :
      (trace finiteFit residue verdict classifier transport replay provenance nameRow : BHist) →
      OpenFitResidueGateUp
  deriving DecidableEq

def openFitResidueGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: openFitResidueGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: openFitResidueGateEncodeBHist h

def openFitResidueGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (openFitResidueGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (openFitResidueGateDecodeBHist tail)

private theorem openFitResidueGateDecode_encode :
    ∀ h : BHist, openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def openFitResidueGateToEventFlow : OpenFitResidueGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OpenFitResidueGateUp.mk trace finiteFit residue verdict classifier transport replay
      provenance nameRow =>
      [openFitResidueGateEncodeBHist trace,
        openFitResidueGateEncodeBHist finiteFit,
        openFitResidueGateEncodeBHist residue,
        openFitResidueGateEncodeBHist verdict,
        openFitResidueGateEncodeBHist classifier,
        openFitResidueGateEncodeBHist transport,
        openFitResidueGateEncodeBHist replay,
        openFitResidueGateEncodeBHist provenance,
        openFitResidueGateEncodeBHist nameRow]

def openFitResidueGateFromEventFlow : EventFlow → Option OpenFitResidueGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [trace, finiteFit, residue, verdict, classifier, transport, replay, provenance, nameRow] =>
      some
        (OpenFitResidueGateUp.mk
          (openFitResidueGateDecodeBHist trace)
          (openFitResidueGateDecodeBHist finiteFit)
          (openFitResidueGateDecodeBHist residue)
          (openFitResidueGateDecodeBHist verdict)
          (openFitResidueGateDecodeBHist classifier)
          (openFitResidueGateDecodeBHist transport)
          (openFitResidueGateDecodeBHist replay)
          (openFitResidueGateDecodeBHist provenance)
          (openFitResidueGateDecodeBHist nameRow))
  | _ => none

private theorem openFitResidueGate_round_trip :
    ∀ x : OpenFitResidueGateUp,
      openFitResidueGateFromEventFlow (openFitResidueGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk trace finiteFit residue verdict classifier transport replay provenance nameRow =>
      change
        some
            (OpenFitResidueGateUp.mk
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist trace))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist finiteFit))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist residue))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist verdict))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist classifier))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist transport))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist replay))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist provenance))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist nameRow))) =
          some
            (OpenFitResidueGateUp.mk trace finiteFit residue verdict classifier transport replay
              provenance nameRow)
      rw [openFitResidueGateDecode_encode trace, openFitResidueGateDecode_encode finiteFit,
        openFitResidueGateDecode_encode residue, openFitResidueGateDecode_encode verdict,
        openFitResidueGateDecode_encode classifier, openFitResidueGateDecode_encode transport,
        openFitResidueGateDecode_encode replay, openFitResidueGateDecode_encode provenance,
        openFitResidueGateDecode_encode nameRow]

private theorem openFitResidueGateToEventFlow_injective {x y : OpenFitResidueGateUp} :
    openFitResidueGateToEventFlow x = openFitResidueGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      openFitResidueGateFromEventFlow (openFitResidueGateToEventFlow x) =
        openFitResidueGateFromEventFlow (openFitResidueGateToEventFlow y) :=
    congrArg openFitResidueGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (openFitResidueGate_round_trip x).symm
      (Eq.trans hread (openFitResidueGate_round_trip y)))

private def openFitResidueGateFields : OpenFitResidueGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OpenFitResidueGateUp.mk trace finiteFit residue verdict classifier transport replay
      provenance nameRow =>
      [trace, finiteFit, residue, verdict, classifier, transport, replay, provenance, nameRow]

private theorem openFitResidueGate_field_faithful :
    ∀ x y : OpenFitResidueGateUp, openFitResidueGateFields x = openFitResidueGateFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk trace finiteFit residue verdict classifier transport replay provenance nameRow =>
      cases y with
      | mk trace' finiteFit' residue' verdict' classifier' transport' replay' provenance'
          nameRow' =>
          cases hfields
          rfl

instance openFitResidueGateBHistCarrier : BHistCarrier OpenFitResidueGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := openFitResidueGateToEventFlow
  fromEventFlow := openFitResidueGateFromEventFlow

instance openFitResidueGateFieldFaithful : FieldFaithful OpenFitResidueGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := openFitResidueGateFields
  field_faithful := openFitResidueGate_field_faithful

instance openFitResidueGateChapterTasteGate : ChapterTasteGate OpenFitResidueGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change openFitResidueGateFromEventFlow (openFitResidueGateToEventFlow x) = some x
    exact openFitResidueGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (openFitResidueGateToEventFlow_injective heq)

instance openFitResidueGateNontrivial : Nontrivial OpenFitResidueGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OpenFitResidueGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OpenFitResidueGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OpenFitResidueGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  openFitResidueGateChapterTasteGate

end BEDC.Derived.OpenFitResidueGateUp
