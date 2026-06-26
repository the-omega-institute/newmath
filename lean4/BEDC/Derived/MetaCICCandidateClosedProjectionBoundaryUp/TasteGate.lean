import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICCandidateClosedProjectionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICCandidateClosedProjectionBoundaryUp : Type where
  | mk (typed candidate router endpoint normal obstruction transport replay provenance namecert :
      BHist) : MetaCICCandidateClosedProjectionBoundaryUp
  deriving DecidableEq

def metaCICCandidateClosedProjectionBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICCandidateClosedProjectionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICCandidateClosedProjectionBoundaryEncodeBHist h

def metaCICCandidateClosedProjectionBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICCandidateClosedProjectionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICCandidateClosedProjectionBoundaryDecodeBHist tail)

private theorem MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICCandidateClosedProjectionBoundaryFields :
    MetaCICCandidateClosedProjectionBoundaryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICCandidateClosedProjectionBoundaryUp.mk typed candidate router endpoint normal
      obstruction transport replay provenance namecert =>
      [typed, candidate, router, endpoint, normal, obstruction, transport, replay,
        provenance, namecert]

def metaCICCandidateClosedProjectionBoundaryToEventFlow :
    MetaCICCandidateClosedProjectionBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICCandidateClosedProjectionBoundaryFields x).map
      metaCICCandidateClosedProjectionBoundaryEncodeBHist

private def metaCICCandidateClosedProjectionBoundaryEventAt :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metaCICCandidateClosedProjectionBoundaryEventAt index rest

def metaCICCandidateClosedProjectionBoundaryFromEventFlow
    (ef : EventFlow) : Option MetaCICCandidateClosedProjectionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICCandidateClosedProjectionBoundaryUp.mk
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 0 ef))
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 1 ef))
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 2 ef))
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 3 ef))
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 4 ef))
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 5 ef))
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 6 ef))
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 7 ef))
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 8 ef))
      (metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEventAt 9 ef)))

private theorem MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICCandidateClosedProjectionBoundaryUp) :
    metaCICCandidateClosedProjectionBoundaryFromEventFlow
      (metaCICCandidateClosedProjectionBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk typed candidate router endpoint normal obstruction transport replay provenance namecert =>
      change
        some
          (MetaCICCandidateClosedProjectionBoundaryUp.mk
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist typed))
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist candidate))
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist router))
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist endpoint))
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist normal))
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist obstruction))
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist transport))
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist replay))
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist provenance))
            (metaCICCandidateClosedProjectionBoundaryDecodeBHist
              (metaCICCandidateClosedProjectionBoundaryEncodeBHist namecert))) =
          some
            (MetaCICCandidateClosedProjectionBoundaryUp.mk typed candidate router endpoint
              normal obstruction transport replay provenance namecert)
      rw [MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode typed,
        MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode candidate,
        MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode router,
        MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode endpoint,
        MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode normal,
        MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode obstruction,
        MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode transport,
        MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode replay,
        MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode provenance,
        MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode namecert]

private theorem MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_injective
    {x y : MetaCICCandidateClosedProjectionBoundaryUp} :
    metaCICCandidateClosedProjectionBoundaryToEventFlow x =
      metaCICCandidateClosedProjectionBoundaryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICCandidateClosedProjectionBoundaryFromEventFlow
          (metaCICCandidateClosedProjectionBoundaryToEventFlow x) =
        metaCICCandidateClosedProjectionBoundaryFromEventFlow
          (metaCICCandidateClosedProjectionBoundaryToEventFlow y) :=
    congrArg metaCICCandidateClosedProjectionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_fields :
    forall x y : MetaCICCandidateClosedProjectionBoundaryUp,
      metaCICCandidateClosedProjectionBoundaryFields x =
        metaCICCandidateClosedProjectionBoundaryFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk typed₁ candidate₁ router₁ endpoint₁ normal₁ obstruction₁ transport₁ replay₁ provenance₁ namecert₁ =>
      cases y with
      | mk typed₂ candidate₂ router₂ endpoint₂ normal₂ obstruction₂ transport₂ replay₂ provenance₂ namecert₂ =>
          cases hfields
          rfl

instance metaCICCandidateClosedProjectionBoundaryBHistCarrier :
    BHistCarrier MetaCICCandidateClosedProjectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICCandidateClosedProjectionBoundaryToEventFlow
  fromEventFlow := metaCICCandidateClosedProjectionBoundaryFromEventFlow

instance metaCICCandidateClosedProjectionBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICCandidateClosedProjectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICCandidateClosedProjectionBoundaryFromEventFlow
        (metaCICCandidateClosedProjectionBoundaryToEventFlow x) = some x
    exact MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_injective heq)

instance metaCICCandidateClosedProjectionBoundaryFieldFaithful :
    FieldFaithful MetaCICCandidateClosedProjectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICCandidateClosedProjectionBoundaryFields
  field_faithful :=
    MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_fields

instance metaCICCandidateClosedProjectionBoundaryNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetaCICCandidateClosedProjectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICCandidateClosedProjectionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICCandidateClosedProjectionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MetaCICCandidateClosedProjectionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICCandidateClosedProjectionBoundaryChapterTasteGate

theorem MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICCandidateClosedProjectionBoundaryDecodeBHist
        (metaCICCandidateClosedProjectionBoundaryEncodeBHist h) = h) ∧
      (∀ x : MetaCICCandidateClosedProjectionBoundaryUp,
        metaCICCandidateClosedProjectionBoundaryFromEventFlow
          (metaCICCandidateClosedProjectionBoundaryToEventFlow x) = some x) ∧
        (∀ x y : MetaCICCandidateClosedProjectionBoundaryUp,
          metaCICCandidateClosedProjectionBoundaryToEventFlow x =
            metaCICCandidateClosedProjectionBoundaryToEventFlow y → x = y) ∧
          metaCICCandidateClosedProjectionBoundaryEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MetaCICCandidateClosedProjectionBoundaryTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.MetaCICCandidateClosedProjectionBoundaryUp
