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
      (traceRequest finiteFit openResidue verdict classifier transport replay provenance
        nameCert : BHist) →
      OpenFitResidueGateUp

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

private theorem openFitResidueGateDecode_encode_bhist :
    ∀ h : BHist, openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def openFitResidueGateFields : OpenFitResidueGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OpenFitResidueGateUp.mk traceRequest finiteFit openResidue verdict classifier transport
      replay provenance nameCert =>
      [traceRequest, finiteFit, openResidue, verdict, classifier, transport, replay,
        provenance, nameCert]

def openFitResidueGateToEventFlow : OpenFitResidueGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OpenFitResidueGateUp.mk traceRequest finiteFit openResidue verdict classifier transport
      replay provenance nameCert =>
      [[BMark.b0],
        openFitResidueGateEncodeBHist traceRequest,
        [BMark.b1, BMark.b0],
        openFitResidueGateEncodeBHist finiteFit,
        [BMark.b1, BMark.b1, BMark.b0],
        openFitResidueGateEncodeBHist openResidue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        openFitResidueGateEncodeBHist verdict,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        openFitResidueGateEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        openFitResidueGateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        openFitResidueGateEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        openFitResidueGateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        openFitResidueGateEncodeBHist nameCert]

private def openFitResidueGateEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => openFitResidueGateEventAtDefault index rest

def openFitResidueGateFromEventFlow (ef : EventFlow) : Option OpenFitResidueGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OpenFitResidueGateUp.mk
      (openFitResidueGateDecodeBHist (openFitResidueGateEventAtDefault 1 ef))
      (openFitResidueGateDecodeBHist (openFitResidueGateEventAtDefault 3 ef))
      (openFitResidueGateDecodeBHist (openFitResidueGateEventAtDefault 5 ef))
      (openFitResidueGateDecodeBHist (openFitResidueGateEventAtDefault 7 ef))
      (openFitResidueGateDecodeBHist (openFitResidueGateEventAtDefault 9 ef))
      (openFitResidueGateDecodeBHist (openFitResidueGateEventAtDefault 11 ef))
      (openFitResidueGateDecodeBHist (openFitResidueGateEventAtDefault 13 ef))
      (openFitResidueGateDecodeBHist (openFitResidueGateEventAtDefault 15 ef))
      (openFitResidueGateDecodeBHist (openFitResidueGateEventAtDefault 17 ef)))

private theorem openFitResidueGate_round_trip :
    ∀ x : OpenFitResidueGateUp,
      openFitResidueGateFromEventFlow (openFitResidueGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk traceRequest finiteFit openResidue verdict classifier transport replay provenance
      nameCert =>
      change
        some
            (OpenFitResidueGateUp.mk
              (openFitResidueGateDecodeBHist
                (openFitResidueGateEncodeBHist traceRequest))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist finiteFit))
              (openFitResidueGateDecodeBHist
                (openFitResidueGateEncodeBHist openResidue))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist verdict))
              (openFitResidueGateDecodeBHist
                (openFitResidueGateEncodeBHist classifier))
              (openFitResidueGateDecodeBHist
                (openFitResidueGateEncodeBHist transport))
              (openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist replay))
              (openFitResidueGateDecodeBHist
                (openFitResidueGateEncodeBHist provenance))
              (openFitResidueGateDecodeBHist
                (openFitResidueGateEncodeBHist nameCert))) =
          some
            (OpenFitResidueGateUp.mk traceRequest finiteFit openResidue verdict classifier
              transport replay provenance nameCert)
      rw [openFitResidueGateDecode_encode_bhist traceRequest,
        openFitResidueGateDecode_encode_bhist finiteFit,
        openFitResidueGateDecode_encode_bhist openResidue,
        openFitResidueGateDecode_encode_bhist verdict,
        openFitResidueGateDecode_encode_bhist classifier,
        openFitResidueGateDecode_encode_bhist transport,
        openFitResidueGateDecode_encode_bhist replay,
        openFitResidueGateDecode_encode_bhist provenance,
        openFitResidueGateDecode_encode_bhist nameCert]

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

private theorem openFitResidueGate_field_faithful_concrete :
    ∀ x y : OpenFitResidueGateUp, openFitResidueGateFields x = openFitResidueGateFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk traceRequest finiteFit openResidue verdict classifier transport replay provenance
      nameCert =>
      cases y with
      | mk traceRequest' finiteFit' openResidue' verdict' classifier' transport' replay'
          provenance' nameCert' =>
          change
            [traceRequest, finiteFit, openResidue, verdict, classifier, transport, replay,
                provenance, nameCert] =
              [traceRequest', finiteFit', openResidue', verdict', classifier', transport',
                replay', provenance', nameCert'] at hfields
          injection hfields with hTrace hTail0
          injection hTail0 with hFit hTail1
          injection hTail1 with hResidue hTail2
          injection hTail2 with hVerdict hTail3
          injection hTail3 with hClassifier hTail4
          injection hTail4 with hTransport hTail5
          injection hTail5 with hReplay hTail6
          injection hTail6 with hProvenance hTail7
          injection hTail7 with hName _hNil
          cases hTrace
          cases hFit
          cases hResidue
          cases hVerdict
          cases hClassifier
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hName
          rfl

instance openFitResidueGateBHistCarrier : BHistCarrier OpenFitResidueGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := openFitResidueGateToEventFlow
  fromEventFlow := openFitResidueGateFromEventFlow

instance openFitResidueGateChapterTasteGate :
    ChapterTasteGate OpenFitResidueGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change openFitResidueGateFromEventFlow (openFitResidueGateToEventFlow x) = some x
    exact openFitResidueGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (openFitResidueGateToEventFlow_injective heq)

instance openFitResidueGateFieldFaithful : FieldFaithful OpenFitResidueGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := openFitResidueGateFields
  field_faithful := openFitResidueGate_field_faithful_concrete

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

theorem OpenFitResidueGateTasteGate_single_carrier_alignment :
    openFitResidueGateDecodeBHist (openFitResidueGateEncodeBHist BHist.Empty) =
        BHist.Empty ∧
      (∀ x : OpenFitResidueGateUp,
        openFitResidueGateFromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      (∀ x y : OpenFitResidueGateUp, BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y →
        x = y) ∧
      Nonempty (ChapterTasteGate OpenFitResidueGateUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · intro x
      change openFitResidueGateFromEventFlow (openFitResidueGateToEventFlow x) = some x
      exact openFitResidueGate_round_trip x
    · constructor
      · intro x y heq
        change openFitResidueGateToEventFlow x = openFitResidueGateToEventFlow y at heq
        exact openFitResidueGateToEventFlow_injective heq
      · exact ⟨openFitResidueGateChapterTasteGate⟩

end BEDC.Derived.OpenFitResidueGateUp
