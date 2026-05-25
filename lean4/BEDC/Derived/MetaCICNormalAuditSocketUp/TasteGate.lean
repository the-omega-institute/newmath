import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICNormalAuditSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICNormalAuditSocketUp : Type where
  | mk :
      (closedTerm candidate closedCandidate candidateSet obstruction frontier transport replay
        provenance localName : BHist) →
        MetaCICNormalAuditSocketUp
  deriving DecidableEq

def metaCICNormalAuditSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICNormalAuditSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICNormalAuditSocketEncodeBHist h

def metaCICNormalAuditSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICNormalAuditSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICNormalAuditSocketDecodeBHist tail)

private theorem MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICNormalAuditSocketFields : MetaCICNormalAuditSocketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICNormalAuditSocketUp.mk closedTerm candidate closedCandidate candidateSet obstruction
      frontier transport replay provenance localName =>
      [closedTerm, candidate, closedCandidate, candidateSet, obstruction, frontier, transport,
        replay, provenance, localName]

def metaCICNormalAuditSocketToEventFlow : MetaCICNormalAuditSocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICNormalAuditSocketFields x).map metaCICNormalAuditSocketEncodeBHist

private def metaCICNormalAuditSocketEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICNormalAuditSocketEventAtDefault index rest

def metaCICNormalAuditSocketFromEventFlow :
    EventFlow → Option MetaCICNormalAuditSocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetaCICNormalAuditSocketUp.mk
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 0 ef))
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 1 ef))
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 2 ef))
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 3 ef))
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 4 ef))
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 5 ef))
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 6 ef))
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 7 ef))
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 8 ef))
        (metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEventAtDefault 9 ef)))

private theorem MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetaCICNormalAuditSocketUp,
      metaCICNormalAuditSocketFromEventFlow
        (metaCICNormalAuditSocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk closedTerm candidate closedCandidate candidateSet obstruction frontier transport replay
      provenance localName =>
      change
        some
          (MetaCICNormalAuditSocketUp.mk
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist closedTerm))
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist candidate))
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist closedCandidate))
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist candidateSet))
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist obstruction))
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist frontier))
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist transport))
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist replay))
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist provenance))
            (metaCICNormalAuditSocketDecodeBHist
              (metaCICNormalAuditSocketEncodeBHist localName))) =
          some
            (MetaCICNormalAuditSocketUp.mk closedTerm candidate closedCandidate candidateSet
              obstruction frontier transport replay provenance localName)
      rw [MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode closedTerm,
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode candidate,
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode closedCandidate,
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode candidateSet,
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode obstruction,
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode frontier,
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode transport,
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode replay,
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode provenance,
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode localName]

private theorem MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetaCICNormalAuditSocketUp} :
    metaCICNormalAuditSocketToEventFlow x = metaCICNormalAuditSocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICNormalAuditSocketFromEventFlow (metaCICNormalAuditSocketToEventFlow x) =
        metaCICNormalAuditSocketFromEventFlow (metaCICNormalAuditSocketToEventFlow y) :=
    congrArg metaCICNormalAuditSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetaCICNormalAuditSocketUp,
      metaCICNormalAuditSocketFields x = metaCICNormalAuditSocketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk closedTerm₁ candidate₁ closedCandidate₁ candidateSet₁ obstruction₁ frontier₁
      transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk closedTerm₂ candidate₂ closedCandidate₂ candidateSet₂ obstruction₂ frontier₂
          transport₂ replay₂ provenance₂ localName₂ =>
          change
            [closedTerm₁, candidate₁, closedCandidate₁, candidateSet₁, obstruction₁,
              frontier₁, transport₁, replay₁, provenance₁, localName₁] =
              [closedTerm₂, candidate₂, closedCandidate₂, candidateSet₂, obstruction₂,
                frontier₂, transport₂, replay₂, provenance₂, localName₂] at hfields
          injection hfields with hClosedTerm tail0
          injection tail0 with hCandidate tail1
          injection tail1 with hClosedCandidate tail2
          injection tail2 with hCandidateSet tail3
          injection tail3 with hObstruction tail4
          injection tail4 with hFrontier tail5
          injection tail5 with hTransport tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hLocalName _
          subst hClosedTerm
          subst hCandidate
          subst hClosedCandidate
          subst hCandidateSet
          subst hObstruction
          subst hFrontier
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance metaCICNormalAuditSocketBHistCarrier : BHistCarrier MetaCICNormalAuditSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICNormalAuditSocketToEventFlow
  fromEventFlow := metaCICNormalAuditSocketFromEventFlow

instance metaCICNormalAuditSocketChapterTasteGate :
    ChapterTasteGate MetaCICNormalAuditSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICNormalAuditSocketFromEventFlow
        (metaCICNormalAuditSocketToEventFlow x) = some x
    exact MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metaCICNormalAuditSocketFieldFaithful :
    FieldFaithful MetaCICNormalAuditSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICNormalAuditSocketFields
  field_faithful := MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_fields

instance metaCICNormalAuditSocketNontrivial :
    Nontrivial MetaCICNormalAuditSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICNormalAuditSocketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICNormalAuditSocketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICNormalAuditSocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICNormalAuditSocketChapterTasteGate

theorem MetaCICNormalAuditSocketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICNormalAuditSocketDecodeBHist (metaCICNormalAuditSocketEncodeBHist h) = h) ∧
      (∀ x : MetaCICNormalAuditSocketUp,
        metaCICNormalAuditSocketFromEventFlow
          (metaCICNormalAuditSocketToEventFlow x) = some x) ∧
        (∀ x y : MetaCICNormalAuditSocketUp,
          metaCICNormalAuditSocketToEventFlow x = metaCICNormalAuditSocketToEventFlow y ->
            x = y) ∧
          metaCICNormalAuditSocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_decode_encode,
      MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetaCICNormalAuditSocketTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICNormalAuditSocketUp
