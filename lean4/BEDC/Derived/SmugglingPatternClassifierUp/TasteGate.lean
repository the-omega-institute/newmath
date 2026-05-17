import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SmugglingPatternClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SmugglingPatternClassifierUp : Type where
  | mk :
      (externalSupply internalRequest refusalGate siblingProvenance transport replay
        provenance localName : BHist) →
      SmugglingPatternClassifierUp
  deriving DecidableEq

def smugglingPatternClassifierEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: smugglingPatternClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: smugglingPatternClassifierEncodeBHist h

def smugglingPatternClassifierDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (smugglingPatternClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (smugglingPatternClassifierDecodeBHist tail)

private theorem smugglingPatternClassifierDecode_encode_bhist :
    ∀ h : BHist,
      smugglingPatternClassifierDecodeBHist
        (smugglingPatternClassifierEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def smugglingPatternClassifierFields :
    SmugglingPatternClassifierUp → List BHist
  | SmugglingPatternClassifierUp.mk externalSupply internalRequest refusalGate
      siblingProvenance transport replay provenance localName =>
      [externalSupply, internalRequest, refusalGate, siblingProvenance, transport, replay,
        provenance, localName]

def smugglingPatternClassifierToEventFlow :
    SmugglingPatternClassifierUp → EventFlow
  | x => (smugglingPatternClassifierFields x).map smugglingPatternClassifierEncodeBHist

private def smugglingPatternClassifierEventAtDefault :
    Nat → EventFlow → RawEvent
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => smugglingPatternClassifierEventAtDefault index rest

def smugglingPatternClassifierFromEventFlow :
    EventFlow → Option SmugglingPatternClassifierUp
  | ef =>
      some
        (SmugglingPatternClassifierUp.mk
          (smugglingPatternClassifierDecodeBHist
            (smugglingPatternClassifierEventAtDefault 0 ef))
          (smugglingPatternClassifierDecodeBHist
            (smugglingPatternClassifierEventAtDefault 1 ef))
          (smugglingPatternClassifierDecodeBHist
            (smugglingPatternClassifierEventAtDefault 2 ef))
          (smugglingPatternClassifierDecodeBHist
            (smugglingPatternClassifierEventAtDefault 3 ef))
          (smugglingPatternClassifierDecodeBHist
            (smugglingPatternClassifierEventAtDefault 4 ef))
          (smugglingPatternClassifierDecodeBHist
            (smugglingPatternClassifierEventAtDefault 5 ef))
          (smugglingPatternClassifierDecodeBHist
            (smugglingPatternClassifierEventAtDefault 6 ef))
          (smugglingPatternClassifierDecodeBHist
            (smugglingPatternClassifierEventAtDefault 7 ef)))

private theorem smugglingPatternClassifier_round_trip :
    ∀ x : SmugglingPatternClassifierUp,
      smugglingPatternClassifierFromEventFlow
        (smugglingPatternClassifierToEventFlow x) = some x := by
  intro x
  cases x with
  | mk externalSupply internalRequest refusalGate siblingProvenance transport replay
      provenance localName =>
      change
        some
          (SmugglingPatternClassifierUp.mk
            (smugglingPatternClassifierDecodeBHist
              (smugglingPatternClassifierEncodeBHist externalSupply))
            (smugglingPatternClassifierDecodeBHist
              (smugglingPatternClassifierEncodeBHist internalRequest))
            (smugglingPatternClassifierDecodeBHist
              (smugglingPatternClassifierEncodeBHist refusalGate))
            (smugglingPatternClassifierDecodeBHist
              (smugglingPatternClassifierEncodeBHist siblingProvenance))
            (smugglingPatternClassifierDecodeBHist
              (smugglingPatternClassifierEncodeBHist transport))
            (smugglingPatternClassifierDecodeBHist
              (smugglingPatternClassifierEncodeBHist replay))
            (smugglingPatternClassifierDecodeBHist
              (smugglingPatternClassifierEncodeBHist provenance))
            (smugglingPatternClassifierDecodeBHist
              (smugglingPatternClassifierEncodeBHist localName))) =
          some
            (SmugglingPatternClassifierUp.mk externalSupply internalRequest refusalGate
              siblingProvenance transport replay provenance localName)
      rw [smugglingPatternClassifierDecode_encode_bhist externalSupply,
        smugglingPatternClassifierDecode_encode_bhist internalRequest,
        smugglingPatternClassifierDecode_encode_bhist refusalGate,
        smugglingPatternClassifierDecode_encode_bhist siblingProvenance,
        smugglingPatternClassifierDecode_encode_bhist transport,
        smugglingPatternClassifierDecode_encode_bhist replay,
        smugglingPatternClassifierDecode_encode_bhist provenance,
        smugglingPatternClassifierDecode_encode_bhist localName]

private theorem smugglingPatternClassifierToEventFlow_injective
    {x y : SmugglingPatternClassifierUp} :
    smugglingPatternClassifierToEventFlow x =
      smugglingPatternClassifierToEventFlow y → x = y := by
  intro heq
  have hread :
      smugglingPatternClassifierFromEventFlow
          (smugglingPatternClassifierToEventFlow x) =
        smugglingPatternClassifierFromEventFlow
          (smugglingPatternClassifierToEventFlow y) :=
    congrArg smugglingPatternClassifierFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (smugglingPatternClassifier_round_trip x).symm
        (Eq.trans hread (smugglingPatternClassifier_round_trip y)))

private theorem smugglingPatternClassifier_fields_faithful :
    ∀ x y : SmugglingPatternClassifierUp,
      smugglingPatternClassifierFields x =
        smugglingPatternClassifierFields y → x = y := by
  intro x y hfields
  cases x with
  | mk externalSupply internalRequest refusalGate siblingProvenance transport replay
      provenance localName =>
      cases y with
      | mk externalSupply' internalRequest' refusalGate' siblingProvenance' transport' replay'
          provenance' localName' =>
          injection hfields with hExternalSupply htail0
          injection htail0 with hInternalRequest htail1
          injection htail1 with hRefusalGate htail2
          injection htail2 with hSiblingProvenance htail3
          injection htail3 with hTransport htail4
          injection htail4 with hReplay htail5
          injection htail5 with hProvenance htail6
          injection htail6 with hLocalName _
          cases hExternalSupply
          cases hInternalRequest
          cases hRefusalGate
          cases hSiblingProvenance
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hLocalName
          rfl

instance smugglingPatternClassifierBHistCarrier :
    BHistCarrier SmugglingPatternClassifierUp where
  toEventFlow := smugglingPatternClassifierToEventFlow
  fromEventFlow := smugglingPatternClassifierFromEventFlow

instance smugglingPatternClassifierChapterTasteGate :
    ChapterTasteGate SmugglingPatternClassifierUp where
  round_trip := by
    intro x
    exact smugglingPatternClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (smugglingPatternClassifierToEventFlow_injective heq)

instance smugglingPatternClassifierFieldFaithful :
    FieldFaithful SmugglingPatternClassifierUp where
  fields := smugglingPatternClassifierFields
  field_faithful := smugglingPatternClassifier_fields_faithful

instance smugglingPatternClassifierNontrivial :
    Nontrivial SmugglingPatternClassifierUp where
  witness_pair :=
    ⟨SmugglingPatternClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SmugglingPatternClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SmugglingPatternClassifierUp :=
  smugglingPatternClassifierChapterTasteGate

theorem SmugglingPatternClassifierTasteGate_single_carrier_alignment :
    ChapterTasteGate SmugglingPatternClassifierUp ∧
      Nonempty (Nontrivial SmugglingPatternClassifierUp) ∧
        Nonempty (FieldFaithful SmugglingPatternClassifierUp) ∧
          (∀ h : BHist,
            smugglingPatternClassifierDecodeBHist
              (smugglingPatternClassifierEncodeBHist h) = h) ∧
          (∀ x : SmugglingPatternClassifierUp,
            smugglingPatternClassifierFromEventFlow
              (smugglingPatternClassifierToEventFlow x) = some x) ∧
          (∀ x y : SmugglingPatternClassifierUp,
            smugglingPatternClassifierToEventFlow x =
              smugglingPatternClassifierToEventFlow y → x = y) ∧
          smugglingPatternClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact
    ⟨smugglingPatternClassifierChapterTasteGate, ⟨smugglingPatternClassifierNontrivial⟩,
      ⟨smugglingPatternClassifierFieldFaithful⟩,
      smugglingPatternClassifierDecode_encode_bhist, smugglingPatternClassifier_round_trip,
      (fun _ _ heq => smugglingPatternClassifierToEventFlow_injective heq), rfl⟩

end BEDC.Derived.SmugglingPatternClassifierUp
