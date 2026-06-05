import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

/-!
# HyperbolicBoundaryPhaseAuditUp TasteGate carrier.
-/

namespace BEDC.Derived.HyperbolicBoundaryPhaseAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicBoundaryPhaseAuditUp : Type where
  | mk :
      (expansionLedger boundaryGeodesic horocycle phaseLedger boundaryTransport auditVerdict
        transport replay provenance localCert : BHist) →
      HyperbolicBoundaryPhaseAuditUp
  deriving DecidableEq

def hyperbolicBoundaryPhaseAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicBoundaryPhaseAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicBoundaryPhaseAuditEncodeBHist h

def hyperbolicBoundaryPhaseAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicBoundaryPhaseAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicBoundaryPhaseAuditDecodeBHist tail)

theorem HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hyperbolicBoundaryPhaseAuditDecodeBHist
        (hyperbolicBoundaryPhaseAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hyperbolicBoundaryPhaseAuditFields : HyperbolicBoundaryPhaseAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicBoundaryPhaseAuditUp.mk expansionLedger boundaryGeodesic horocycle phaseLedger
      boundaryTransport auditVerdict transport replay provenance localCert =>
      [expansionLedger, boundaryGeodesic, horocycle, phaseLedger, boundaryTransport,
        auditVerdict, transport, replay, provenance, localCert]

def hyperbolicBoundaryPhaseAuditToEventFlow :
    HyperbolicBoundaryPhaseAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicBoundaryPhaseAuditFields x).map hyperbolicBoundaryPhaseAuditEncodeBHist

private def HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault index rest

def hyperbolicBoundaryPhaseAuditFromEventFlow :
    EventFlow → Option HyperbolicBoundaryPhaseAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (HyperbolicBoundaryPhaseAuditUp.mk
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (hyperbolicBoundaryPhaseAuditDecodeBHist
          (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

theorem HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HyperbolicBoundaryPhaseAuditUp,
      hyperbolicBoundaryPhaseAuditFromEventFlow
        (hyperbolicBoundaryPhaseAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk expansionLedger boundaryGeodesic horocycle phaseLedger boundaryTransport auditVerdict
      transport replay provenance localCert =>
      change
        some
          (HyperbolicBoundaryPhaseAuditUp.mk
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist expansionLedger))
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist boundaryGeodesic))
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist horocycle))
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist phaseLedger))
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist boundaryTransport))
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist auditVerdict))
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist transport))
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist replay))
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist provenance))
            (hyperbolicBoundaryPhaseAuditDecodeBHist
              (hyperbolicBoundaryPhaseAuditEncodeBHist localCert))) =
          some
            (HyperbolicBoundaryPhaseAuditUp.mk expansionLedger boundaryGeodesic horocycle
              phaseLedger boundaryTransport auditVerdict transport replay provenance localCert)
      rw [HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode
        expansionLedger,
        HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode
          boundaryGeodesic,
        HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode horocycle,
        HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode phaseLedger,
        HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode
          boundaryTransport,
        HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode auditVerdict,
        HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode transport,
        HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode replay,
        HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode provenance,
        HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode localCert]

theorem HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyperbolicBoundaryPhaseAuditUp} :
    hyperbolicBoundaryPhaseAuditToEventFlow x =
      hyperbolicBoundaryPhaseAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicBoundaryPhaseAuditFromEventFlow
          (hyperbolicBoundaryPhaseAuditToEventFlow x) =
        hyperbolicBoundaryPhaseAuditFromEventFlow
          (hyperbolicBoundaryPhaseAuditToEventFlow y) :=
    congrArg hyperbolicBoundaryPhaseAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_round_trip y)))

theorem HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : HyperbolicBoundaryPhaseAuditUp,
      hyperbolicBoundaryPhaseAuditFields x = hyperbolicBoundaryPhaseAuditFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk expansionLedger₁ boundaryGeodesic₁ horocycle₁ phaseLedger₁ boundaryTransport₁
      auditVerdict₁ transport₁ replay₁ provenance₁ localCert₁ =>
      cases y with
      | mk expansionLedger₂ boundaryGeodesic₂ horocycle₂ phaseLedger₂ boundaryTransport₂
          auditVerdict₂ transport₂ replay₂ provenance₂ localCert₂ =>
          cases hfields
          rfl

instance hyperbolicBoundaryPhaseAuditBHistCarrier :
    BHistCarrier HyperbolicBoundaryPhaseAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicBoundaryPhaseAuditToEventFlow
  fromEventFlow := hyperbolicBoundaryPhaseAuditFromEventFlow

instance hyperbolicBoundaryPhaseAuditChapterTasteGate :
    ChapterTasteGate HyperbolicBoundaryPhaseAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicBoundaryPhaseAuditFromEventFlow
        (hyperbolicBoundaryPhaseAuditToEventFlow x) = some x
    exact HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hyperbolicBoundaryPhaseAuditFieldFaithful :
    FieldFaithful HyperbolicBoundaryPhaseAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicBoundaryPhaseAuditFields
  field_faithful :=
    HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_field_faithful

instance hyperbolicBoundaryPhaseAuditNontrivial :
    BEDC.Meta.TasteGate.Nontrivial HyperbolicBoundaryPhaseAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicBoundaryPhaseAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicBoundaryPhaseAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HyperbolicBoundaryPhaseAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicBoundaryPhaseAuditChapterTasteGate

theorem HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicBoundaryPhaseAuditDecodeBHist
        (hyperbolicBoundaryPhaseAuditEncodeBHist h) = h) ∧
      (∀ x : HyperbolicBoundaryPhaseAuditUp,
        hyperbolicBoundaryPhaseAuditFromEventFlow
          (hyperbolicBoundaryPhaseAuditToEventFlow x) = some x) ∧
        Nonempty (ChapterTasteGate HyperbolicBoundaryPhaseAuditUp) ∧
          hyperbolicBoundaryPhaseAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact HyperbolicBoundaryPhaseAuditTasteGate_single_carrier_alignment_round_trip
    · constructor
      · exact ⟨hyperbolicBoundaryPhaseAuditChapterTasteGate⟩
      · rfl

end BEDC.Derived.HyperbolicBoundaryPhaseAuditUp
