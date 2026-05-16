import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelOutputVerifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelOutputVerifierUp : Type where
  | mk :
      (harness auditChannel modelTrace promptResponse inscriptionAudit verifier proofCheck
        refusal route replay provenance name : BHist) →
      LargeModelOutputVerifierUp
  deriving DecidableEq

def largeModelOutputVerifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: largeModelOutputVerifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: largeModelOutputVerifierEncodeBHist h

def largeModelOutputVerifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (largeModelOutputVerifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (largeModelOutputVerifierDecodeBHist tail)

private theorem largeModelOutputVerifierDecode_encode_bhist :
    ∀ h : BHist,
      largeModelOutputVerifierDecodeBHist
        (largeModelOutputVerifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def largeModelOutputVerifierFields :
    LargeModelOutputVerifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelOutputVerifierUp.mk harness auditChannel modelTrace promptResponse
      inscriptionAudit verifier proofCheck refusal route replay provenance name =>
      [harness, auditChannel, modelTrace, promptResponse, inscriptionAudit, verifier,
        proofCheck, refusal, route, replay, provenance, name]

def largeModelOutputVerifierToEventFlow : LargeModelOutputVerifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (largeModelOutputVerifierFields x).map largeModelOutputVerifierEncodeBHist

def largeModelOutputVerifierFromEventFlow :
    EventFlow → Option LargeModelOutputVerifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | harness :: rest0 =>
      match rest0 with
      | [] => none
      | auditChannel :: rest1 =>
          match rest1 with
          | [] => none
          | modelTrace :: rest2 =>
              match rest2 with
              | [] => none
              | promptResponse :: rest3 =>
                  match rest3 with
                  | [] => none
                  | inscriptionAudit :: rest4 =>
                      match rest4 with
                      | [] => none
                      | verifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | proofCheck :: rest6 =>
                              match rest6 with
                              | [] => none
                              | refusal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | route :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | name :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (LargeModelOutputVerifierUp.mk
                                                          (largeModelOutputVerifierDecodeBHist
                                                            harness)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            auditChannel)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            modelTrace)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            promptResponse)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            inscriptionAudit)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            verifier)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            proofCheck)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            refusal)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            route)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            replay)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            provenance)
                                                          (largeModelOutputVerifierDecodeBHist
                                                            name))
                                                  | _ :: _ => none

private theorem largeModelOutputVerifier_round_trip :
    ∀ x : LargeModelOutputVerifierUp,
      largeModelOutputVerifierFromEventFlow
        (largeModelOutputVerifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk harness auditChannel modelTrace promptResponse inscriptionAudit verifier proofCheck
      refusal route replay provenance name =>
      change
        some
          (LargeModelOutputVerifierUp.mk
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist harness))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist auditChannel))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist modelTrace))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist promptResponse))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist inscriptionAudit))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist verifier))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist proofCheck))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist refusal))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist route))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist replay))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist provenance))
            (largeModelOutputVerifierDecodeBHist
              (largeModelOutputVerifierEncodeBHist name))) =
          some
            (LargeModelOutputVerifierUp.mk harness auditChannel modelTrace promptResponse
              inscriptionAudit verifier proofCheck refusal route replay provenance name)
      rw [largeModelOutputVerifierDecode_encode_bhist harness,
        largeModelOutputVerifierDecode_encode_bhist auditChannel,
        largeModelOutputVerifierDecode_encode_bhist modelTrace,
        largeModelOutputVerifierDecode_encode_bhist promptResponse,
        largeModelOutputVerifierDecode_encode_bhist inscriptionAudit,
        largeModelOutputVerifierDecode_encode_bhist verifier,
        largeModelOutputVerifierDecode_encode_bhist proofCheck,
        largeModelOutputVerifierDecode_encode_bhist refusal,
        largeModelOutputVerifierDecode_encode_bhist route,
        largeModelOutputVerifierDecode_encode_bhist replay,
        largeModelOutputVerifierDecode_encode_bhist provenance,
        largeModelOutputVerifierDecode_encode_bhist name]

private theorem largeModelOutputVerifierToEventFlow_injective
    {x y : LargeModelOutputVerifierUp} :
    largeModelOutputVerifierToEventFlow x =
      largeModelOutputVerifierToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelOutputVerifierFromEventFlow (largeModelOutputVerifierToEventFlow x) =
        largeModelOutputVerifierFromEventFlow (largeModelOutputVerifierToEventFlow y) :=
    congrArg largeModelOutputVerifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelOutputVerifier_round_trip x).symm
      (Eq.trans hread (largeModelOutputVerifier_round_trip y)))

private theorem largeModelOutputVerifier_fields_faithful :
    ∀ x y : LargeModelOutputVerifierUp,
      largeModelOutputVerifierFields x = largeModelOutputVerifierFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk harness₁ auditChannel₁ modelTrace₁ promptResponse₁ inscriptionAudit₁ verifier₁
      proofCheck₁ refusal₁ route₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk harness₂ auditChannel₂ modelTrace₂ promptResponse₂ inscriptionAudit₂ verifier₂
          proofCheck₂ refusal₂ route₂ replay₂ provenance₂ name₂ =>
          injection h with hHarness t1
          injection t1 with hAuditChannel t2
          injection t2 with hModelTrace t3
          injection t3 with hPromptResponse t4
          injection t4 with hInscriptionAudit t5
          injection t5 with hVerifier t6
          injection t6 with hProofCheck t7
          injection t7 with hRefusal t8
          injection t8 with hRoute t9
          injection t9 with hReplay t10
          injection t10 with hProvenance t11
          injection t11 with hName _
          subst hHarness
          subst hAuditChannel
          subst hModelTrace
          subst hPromptResponse
          subst hInscriptionAudit
          subst hVerifier
          subst hProofCheck
          subst hRefusal
          subst hRoute
          subst hReplay
          subst hProvenance
          subst hName
          rfl

instance largeModelOutputVerifierBHistCarrier :
    BHistCarrier LargeModelOutputVerifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelOutputVerifierToEventFlow
  fromEventFlow := largeModelOutputVerifierFromEventFlow

instance largeModelOutputVerifierChapterTasteGate :
    ChapterTasteGate LargeModelOutputVerifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      largeModelOutputVerifierFromEventFlow
        (largeModelOutputVerifierToEventFlow x) = some x
    exact largeModelOutputVerifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelOutputVerifierToEventFlow_injective heq)

instance largeModelOutputVerifierFieldFaithful :
    FieldFaithful LargeModelOutputVerifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := largeModelOutputVerifierFields
  field_faithful := largeModelOutputVerifier_fields_faithful

instance largeModelOutputVerifierNontrivial :
    Nontrivial LargeModelOutputVerifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LargeModelOutputVerifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LargeModelOutputVerifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LargeModelOutputVerifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  largeModelOutputVerifierChapterTasteGate

theorem LargeModelOutputVerifierTasteGate_single_carrier_alignment :
    (forall h : BHist,
      largeModelOutputVerifierDecodeBHist
        (largeModelOutputVerifierEncodeBHist h) = h) ∧
      (forall x : LargeModelOutputVerifierUp,
        largeModelOutputVerifierFromEventFlow
          (largeModelOutputVerifierToEventFlow x) = some x) ∧
        (forall x y : LargeModelOutputVerifierUp,
          largeModelOutputVerifierToEventFlow x =
            largeModelOutputVerifierToEventFlow y -> x = y) ∧
          largeModelOutputVerifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact largeModelOutputVerifierDecode_encode_bhist
  · constructor
    · exact largeModelOutputVerifier_round_trip
    · constructor
      · intro x y heq
        exact largeModelOutputVerifierToEventFlow_injective heq
      · rfl

end BEDC.Derived.LargeModelOutputVerifierUp
