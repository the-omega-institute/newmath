import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VerificationFailureRoadmapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VerificationFailureRoadmapUp : Type where
  | mk :
      (report audit failure downgrade roadmap upgrade cannotClaim transport replay provenance
        name : BHist) →
        VerificationFailureRoadmapUp
  deriving DecidableEq

def verificationFailureRoadmapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: verificationFailureRoadmapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: verificationFailureRoadmapEncodeBHist h

def verificationFailureRoadmapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (verificationFailureRoadmapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (verificationFailureRoadmapDecodeBHist tail)

private theorem verificationFailureRoadmap_decode_encode_bhist :
    ∀ h : BHist,
      verificationFailureRoadmapDecodeBHist
        (verificationFailureRoadmapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def verificationFailureRoadmapFields :
    VerificationFailureRoadmapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VerificationFailureRoadmapUp.mk report audit failure downgrade roadmap upgrade cannotClaim
      transport replay provenance name =>
      [report, audit, failure, downgrade, roadmap, upgrade, cannotClaim, transport, replay,
        provenance, name]

def verificationFailureRoadmapToEventFlow :
    VerificationFailureRoadmapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map verificationFailureRoadmapEncodeBHist (verificationFailureRoadmapFields x)

def verificationFailureRoadmapFromEventFlow :
    EventFlow → Option VerificationFailureRoadmapUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | report :: rest0 =>
      match rest0 with
      | [] => none
      | audit :: rest1 =>
          match rest1 with
          | [] => none
          | failure :: rest2 =>
              match rest2 with
              | [] => none
              | downgrade :: rest3 =>
                  match rest3 with
                  | [] => none
                  | roadmap :: rest4 =>
                      match rest4 with
                      | [] => none
                      | upgrade :: rest5 =>
                          match rest5 with
                          | [] => none
                          | cannotClaim :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | name :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (VerificationFailureRoadmapUp.mk
                                                      (verificationFailureRoadmapDecodeBHist
                                                        report)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        audit)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        failure)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        downgrade)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        roadmap)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        upgrade)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        cannotClaim)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        transport)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        replay)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        provenance)
                                                      (verificationFailureRoadmapDecodeBHist
                                                        name))
                                              | _ :: _ => none

private theorem verificationFailureRoadmap_round_trip :
    ∀ x : VerificationFailureRoadmapUp,
      verificationFailureRoadmapFromEventFlow
        (verificationFailureRoadmapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk report audit failure downgrade roadmap upgrade cannotClaim transport replay provenance
      name =>
      change
        some
          (VerificationFailureRoadmapUp.mk
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist report))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist audit))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist failure))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist downgrade))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist roadmap))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist upgrade))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist cannotClaim))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist transport))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist replay))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist provenance))
            (verificationFailureRoadmapDecodeBHist
              (verificationFailureRoadmapEncodeBHist name))) =
          some
            (VerificationFailureRoadmapUp.mk report audit failure downgrade roadmap upgrade
              cannotClaim transport replay provenance name)
      rw [verificationFailureRoadmap_decode_encode_bhist report,
        verificationFailureRoadmap_decode_encode_bhist audit,
        verificationFailureRoadmap_decode_encode_bhist failure,
        verificationFailureRoadmap_decode_encode_bhist downgrade,
        verificationFailureRoadmap_decode_encode_bhist roadmap,
        verificationFailureRoadmap_decode_encode_bhist upgrade,
        verificationFailureRoadmap_decode_encode_bhist cannotClaim,
        verificationFailureRoadmap_decode_encode_bhist transport,
        verificationFailureRoadmap_decode_encode_bhist replay,
        verificationFailureRoadmap_decode_encode_bhist provenance,
        verificationFailureRoadmap_decode_encode_bhist name]

private theorem verificationFailureRoadmapToEventFlow_injective
    {x y : VerificationFailureRoadmapUp} :
    verificationFailureRoadmapToEventFlow x =
      verificationFailureRoadmapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      verificationFailureRoadmapFromEventFlow (verificationFailureRoadmapToEventFlow x) =
        verificationFailureRoadmapFromEventFlow (verificationFailureRoadmapToEventFlow y) :=
    congrArg verificationFailureRoadmapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (verificationFailureRoadmap_round_trip x).symm
      (Eq.trans hread (verificationFailureRoadmap_round_trip y)))

private theorem verificationFailureRoadmap_field_faithful :
    ∀ x y : VerificationFailureRoadmapUp,
      verificationFailureRoadmapFields x = verificationFailureRoadmapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk report₁ audit₁ failure₁ downgrade₁ roadmap₁ upgrade₁ cannotClaim₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk report₂ audit₂ failure₂ downgrade₂ roadmap₂ upgrade₂ cannotClaim₂ transport₂ replay₂
          provenance₂ name₂ =>
          cases h
          rfl

instance verificationFailureRoadmapBHistCarrier :
    BHistCarrier VerificationFailureRoadmapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := verificationFailureRoadmapToEventFlow
  fromEventFlow := verificationFailureRoadmapFromEventFlow

instance verificationFailureRoadmapChapterTasteGate :
    ChapterTasteGate VerificationFailureRoadmapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      verificationFailureRoadmapFromEventFlow
        (verificationFailureRoadmapToEventFlow x) = some x
    exact verificationFailureRoadmap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (verificationFailureRoadmapToEventFlow_injective heq)

instance verificationFailureRoadmapFieldFaithful :
    FieldFaithful VerificationFailureRoadmapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := verificationFailureRoadmapFields
  field_faithful := verificationFailureRoadmap_field_faithful

instance verificationFailureRoadmapNontrivial :
    Nontrivial VerificationFailureRoadmapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨VerificationFailureRoadmapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      VerificationFailureRoadmapUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem verificationFailureRoadmap_taste_gate_surface :
    Nonempty (ChapterTasteGate VerificationFailureRoadmapUp) ∧
      Nonempty (FieldFaithful VerificationFailureRoadmapUp) ∧
        VerificationFailureRoadmapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty ≠
          VerificationFailureRoadmapUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro verificationFailureRoadmapChapterTasteGate,
      Nonempty.intro verificationFailureRoadmapFieldFaithful,
      by
        intro h
        cases h⟩

end BEDC.Derived.VerificationFailureRoadmapUp
