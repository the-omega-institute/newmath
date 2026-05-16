import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedScientificMethodologyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedScientificMethodologyUp : Type where
  | mk :
      (methodologyLedger physicalAudit explanation idealization effectiveDomain leakage
        failure route transport replay provenance localName : BHist) →
      RealityConstrainedScientificMethodologyUp
  deriving DecidableEq

def realityConstrainedScientificMethodologyEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedScientificMethodologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedScientificMethodologyEncodeBHist h

def realityConstrainedScientificMethodologyDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedScientificMethodologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedScientificMethodologyDecodeBHist tail)

private theorem realityConstrainedScientificMethodology_decode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedScientificMethodologyFields :
    RealityConstrainedScientificMethodologyUp → List BHist
  | RealityConstrainedScientificMethodologyUp.mk methodologyLedger physicalAudit explanation
      idealization effectiveDomain leakage failure route transport replay provenance localName =>
      [methodologyLedger, physicalAudit, explanation, idealization, effectiveDomain, leakage,
        failure, route, transport, replay, provenance, localName]

def realityConstrainedScientificMethodologyToEventFlow :
    RealityConstrainedScientificMethodologyUp → EventFlow
  | RealityConstrainedScientificMethodologyUp.mk methodologyLedger physicalAudit explanation
      idealization effectiveDomain leakage failure route transport replay provenance localName =>
      [[BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist methodologyLedger,
        [BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist physicalAudit,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist explanation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist idealization,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist effectiveDomain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist leakage,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedScientificMethodologyEncodeBHist localName]

private def realityConstrainedScientificMethodologyEventAtDefault :
    Nat → EventFlow → RawEvent
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realityConstrainedScientificMethodologyEventAtDefault index rest

def realityConstrainedScientificMethodologyFromEventFlow
    (ef : EventFlow) : Option RealityConstrainedScientificMethodologyUp :=
  some
    (RealityConstrainedScientificMethodologyUp.mk
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 1 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 3 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 5 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 7 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 9 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 11 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 13 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 15 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 17 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 19 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 21 ef))
      (realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEventAtDefault 23 ef)))

private theorem realityConstrainedScientificMethodology_round_trip :
    ∀ x : RealityConstrainedScientificMethodologyUp,
      realityConstrainedScientificMethodologyFromEventFlow
        (realityConstrainedScientificMethodologyToEventFlow x) = some x := by
  intro x
  cases x with
  | mk methodologyLedger physicalAudit explanation idealization effectiveDomain leakage
      failure route transport replay provenance localName =>
      change
        some
          (RealityConstrainedScientificMethodologyUp.mk
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist methodologyLedger))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist physicalAudit))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist explanation))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist idealization))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist effectiveDomain))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist leakage))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist failure))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist route))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist transport))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist replay))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist provenance))
            (realityConstrainedScientificMethodologyDecodeBHist
              (realityConstrainedScientificMethodologyEncodeBHist localName))) =
          some
            (RealityConstrainedScientificMethodologyUp.mk methodologyLedger physicalAudit
              explanation idealization effectiveDomain leakage failure route transport replay
              provenance localName)
      rw [realityConstrainedScientificMethodology_decode_encode_bhist methodologyLedger,
        realityConstrainedScientificMethodology_decode_encode_bhist physicalAudit,
        realityConstrainedScientificMethodology_decode_encode_bhist explanation,
        realityConstrainedScientificMethodology_decode_encode_bhist idealization,
        realityConstrainedScientificMethodology_decode_encode_bhist effectiveDomain,
        realityConstrainedScientificMethodology_decode_encode_bhist leakage,
        realityConstrainedScientificMethodology_decode_encode_bhist failure,
        realityConstrainedScientificMethodology_decode_encode_bhist route,
        realityConstrainedScientificMethodology_decode_encode_bhist transport,
        realityConstrainedScientificMethodology_decode_encode_bhist replay,
        realityConstrainedScientificMethodology_decode_encode_bhist provenance,
        realityConstrainedScientificMethodology_decode_encode_bhist localName]

private theorem realityConstrainedScientificMethodology_injective
    {x y : RealityConstrainedScientificMethodologyUp} :
    realityConstrainedScientificMethodologyToEventFlow x =
      realityConstrainedScientificMethodologyToEventFlow y → x = y := by
  intro heq
  have hread :
      realityConstrainedScientificMethodologyFromEventFlow
          (realityConstrainedScientificMethodologyToEventFlow x) =
        realityConstrainedScientificMethodologyFromEventFlow
          (realityConstrainedScientificMethodologyToEventFlow y) :=
    congrArg realityConstrainedScientificMethodologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (realityConstrainedScientificMethodology_round_trip x).symm
      (Eq.trans hread (realityConstrainedScientificMethodology_round_trip y)))

private theorem realityConstrainedScientificMethodology_fields :
    ∀ x y : RealityConstrainedScientificMethodologyUp,
      realityConstrainedScientificMethodologyFields x =
        realityConstrainedScientificMethodologyFields y → x = y := by
  intro x y hfields
  cases x with
  | mk methodologyLedger₁ physicalAudit₁ explanation₁ idealization₁ effectiveDomain₁
      leakage₁ failure₁ route₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk methodologyLedger₂ physicalAudit₂ explanation₂ idealization₂ effectiveDomain₂
          leakage₂ failure₂ route₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance realityConstrainedScientificMethodologyBHistCarrier :
    BHistCarrier RealityConstrainedScientificMethodologyUp where
  toEventFlow := realityConstrainedScientificMethodologyToEventFlow
  fromEventFlow := realityConstrainedScientificMethodologyFromEventFlow

instance realityConstrainedScientificMethodologyChapterTasteGate :
    ChapterTasteGate RealityConstrainedScientificMethodologyUp where
  round_trip := by
    intro x
    exact realityConstrainedScientificMethodology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedScientificMethodology_injective heq)

instance realityConstrainedScientificMethodologyFieldFaithful :
    FieldFaithful RealityConstrainedScientificMethodologyUp where
  fields := realityConstrainedScientificMethodologyFields
  field_faithful := realityConstrainedScientificMethodology_fields

instance realityConstrainedScientificMethodologyNontrivial :
    Nontrivial RealityConstrainedScientificMethodologyUp where
  witness_pair :=
    ⟨RealityConstrainedScientificMethodologyUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealityConstrainedScientificMethodologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedScientificMethodologyUp :=
  realityConstrainedScientificMethodologyChapterTasteGate

theorem RealityConstrainedScientificMethodologyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedScientificMethodologyDecodeBHist
        (realityConstrainedScientificMethodologyEncodeBHist h) = h) ∧
      Nonempty (Nontrivial RealityConstrainedScientificMethodologyUp) ∧
        Nonempty (ChapterTasteGate RealityConstrainedScientificMethodologyUp) ∧
          Nonempty (FieldFaithful RealityConstrainedScientificMethodologyUp) ∧
            realityConstrainedScientificMethodologyEncodeBHist BHist.Empty =
              ([] : List BMark) := by
  constructor
  · exact realityConstrainedScientificMethodology_decode_encode_bhist
  · constructor
    · exact ⟨realityConstrainedScientificMethodologyNontrivial⟩
    · constructor
      · exact ⟨realityConstrainedScientificMethodologyChapterTasteGate⟩
      · constructor
        · exact ⟨realityConstrainedScientificMethodologyFieldFaithful⟩
        · rfl

end BEDC.Derived.RealityConstrainedScientificMethodologyUp.TasteGate

namespace BEDC.Derived.RealityConstrainedScientificMethodologyUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate
      TasteGate.RealityConstrainedScientificMethodologyUp :=
  TasteGate.taste_gate

end BEDC.Derived.RealityConstrainedScientificMethodologyUp
