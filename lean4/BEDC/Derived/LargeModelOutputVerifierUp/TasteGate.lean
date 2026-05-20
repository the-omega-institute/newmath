import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelOutputVerifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelOutputVerifierUp : Type where
  | mk :
      (harness auditChannel modelTrace promptResponse inscriptionAudit verifier proofCheck
        refusal route replay provenance localName : BHist) → LargeModelOutputVerifierUp
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
      largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def largeModelOutputVerifierToEventFlow : LargeModelOutputVerifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelOutputVerifierUp.mk harness auditChannel modelTrace promptResponse
      inscriptionAudit verifier proofCheck refusal route replay provenance localName =>
      [[BMark.b0],
        largeModelOutputVerifierEncodeBHist harness,
        [BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist auditChannel,
        [BMark.b1, BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist modelTrace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist promptResponse,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist inscriptionAudit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist verifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        largeModelOutputVerifierEncodeBHist proofCheck,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelOutputVerifierEncodeBHist localName]

private def largeModelOutputVerifierRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => largeModelOutputVerifierRawAt n rest

private def largeModelOutputVerifierLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => largeModelOutputVerifierLengthEq n rest

def largeModelOutputVerifierFromEventFlow :
    EventFlow → Option LargeModelOutputVerifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match largeModelOutputVerifierLengthEq 24 flow with
      | true =>
          some
            (LargeModelOutputVerifierUp.mk
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 1 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 3 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 5 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 7 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 9 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 11 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 13 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 15 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 17 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 19 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 21 flow))
              (largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierRawAt 23 flow)))
      | false => none

private theorem largeModelOutputVerifier_round_trip :
    ∀ x : LargeModelOutputVerifierUp,
      largeModelOutputVerifierFromEventFlow (largeModelOutputVerifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk harness auditChannel modelTrace promptResponse inscriptionAudit verifier proofCheck
      refusal route replay provenance localName =>
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
              (largeModelOutputVerifierEncodeBHist localName))) =
          some
            (LargeModelOutputVerifierUp.mk harness auditChannel modelTrace promptResponse
              inscriptionAudit verifier proofCheck refusal route replay provenance localName)
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
        largeModelOutputVerifierDecode_encode_bhist localName]

private theorem largeModelOutputVerifierToEventFlow_injective
    {x y : LargeModelOutputVerifierUp} :
    largeModelOutputVerifierToEventFlow x = largeModelOutputVerifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelOutputVerifierFromEventFlow (largeModelOutputVerifierToEventFlow x) =
        largeModelOutputVerifierFromEventFlow (largeModelOutputVerifierToEventFlow y) :=
    congrArg largeModelOutputVerifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelOutputVerifier_round_trip x).symm
      (Eq.trans hread (largeModelOutputVerifier_round_trip y)))

instance largeModelOutputVerifierBHistCarrier : BHistCarrier LargeModelOutputVerifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelOutputVerifierToEventFlow
  fromEventFlow := largeModelOutputVerifierFromEventFlow

private def largeModelOutputVerifierChapterTasteGateConcrete :
    @ChapterTasteGate LargeModelOutputVerifierUp largeModelOutputVerifierBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change largeModelOutputVerifierFromEventFlow (largeModelOutputVerifierToEventFlow x) =
      some x
    exact largeModelOutputVerifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelOutputVerifierToEventFlow_injective heq)

instance largeModelOutputVerifierChapterTasteGate :
    ChapterTasteGate LargeModelOutputVerifierUp :=
  largeModelOutputVerifierChapterTasteGateConcrete

def largeModelOutputVerifierFields : LargeModelOutputVerifierUp → List BHist
  | LargeModelOutputVerifierUp.mk harness auditChannel modelTrace promptResponse
      inscriptionAudit verifier proofCheck refusal route replay provenance localName =>
      [harness, auditChannel, modelTrace, promptResponse, inscriptionAudit, verifier,
        proofCheck, refusal, route, replay, provenance, localName]

private theorem largeModelOutputVerifier_field_faithful :
    ∀ x y : LargeModelOutputVerifierUp,
      largeModelOutputVerifierFields x = largeModelOutputVerifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  intro x y h
  cases x with
  | mk harness1 auditChannel1 modelTrace1 promptResponse1 inscriptionAudit1 verifier1
      proofCheck1 refusal1 route1 replay1 provenance1 localName1 =>
      cases y with
      | mk harness2 auditChannel2 modelTrace2 promptResponse2 inscriptionAudit2 verifier2
          proofCheck2 refusal2 route2 replay2 provenance2 localName2 =>
          cases h
          rfl

private def largeModelOutputVerifierFieldFaithfulConcrete :
    @FieldFaithful LargeModelOutputVerifierUp largeModelOutputVerifierBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  fields := largeModelOutputVerifierFields
  field_faithful := largeModelOutputVerifier_field_faithful

instance largeModelOutputVerifierFieldFaithful :
    FieldFaithful LargeModelOutputVerifierUp :=
  largeModelOutputVerifierFieldFaithfulConcrete

private def largeModelOutputVerifierWitnessPair :
    Σ' (x : LargeModelOutputVerifierUp) (y : LargeModelOutputVerifierUp), x ≠ y :=
  ⟨LargeModelOutputVerifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty,
    LargeModelOutputVerifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty,
    by
      intro h
      cases h⟩

private def largeModelOutputVerifierNontrivialConcrete :
    Nontrivial LargeModelOutputVerifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := largeModelOutputVerifierWitnessPair

instance largeModelOutputVerifierNontrivial : Nontrivial LargeModelOutputVerifierUp :=
  largeModelOutputVerifierNontrivialConcrete

def taste_gate : ChapterTasteGate LargeModelOutputVerifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  largeModelOutputVerifierChapterTasteGateConcrete

private theorem largeModelOutputVerifier_single_carrier_alignment_concrete :
    (largeModelOutputVerifierEncodeBHist BHist.Empty = ([] : List BMark)) ∧
      (∀ h : BHist,
        largeModelOutputVerifierDecodeBHist
          (largeModelOutputVerifierEncodeBHist h) = h) ∧
        (∀ x : LargeModelOutputVerifierUp,
          largeModelOutputVerifierFromEventFlow
            (largeModelOutputVerifierToEventFlow x) = some x) ∧
          (∀ x y : LargeModelOutputVerifierUp,
            largeModelOutputVerifierToEventFlow x =
                largeModelOutputVerifierToEventFlow y →
              x = y) := by
  exact
    ⟨rfl,
      largeModelOutputVerifierDecode_encode_bhist,
      largeModelOutputVerifier_round_trip,
      fun _ _ heq => largeModelOutputVerifierToEventFlow_injective heq⟩

namespace TasteGate

theorem LargeModelOutputVerifierTasteGate_single_carrier_alignment :
    (largeModelOutputVerifierEncodeBHist BHist.Empty = ([] : List BMark)) ∧
      (∀ h : BHist,
        largeModelOutputVerifierDecodeBHist
          (largeModelOutputVerifierEncodeBHist h) = h) ∧
        (∀ x : LargeModelOutputVerifierUp,
          largeModelOutputVerifierFromEventFlow
            (largeModelOutputVerifierToEventFlow x) = some x) ∧
          (∀ x y : LargeModelOutputVerifierUp,
            largeModelOutputVerifierToEventFlow x =
                largeModelOutputVerifierToEventFlow y →
              x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨rfl,
      largeModelOutputVerifierDecode_encode_bhist,
      largeModelOutputVerifier_round_trip,
      fun _ _ heq => largeModelOutputVerifierToEventFlow_injective heq⟩

end TasteGate

theorem LargeModelOutputVerifierUp_StdBridge [AskSetup] [PackageSetup]
    {Q C R verifierProof publicRoute : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    Cont Q C verifierProof ->
      Cont verifierProof R publicRoute ->
        PkgSig bundle publicRoute pkg ->
          SemanticNameCert
            (fun row : BHist =>
              hsame row publicRoute ∧ Cont Q C verifierProof ∧
                Cont verifierProof R publicRoute)
            (fun row : BHist => hsame row publicRoute ∧ Cont Q C verifierProof)
            (fun row : BHist => hsame row publicRoute ∧ PkgSig bundle publicRoute pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro verifierRoute publicVerifier packageRoute
  have verifierRouteStable : Cont Q C verifierProof :=
    cont_result_hsame_transport verifierRoute (hsame_refl verifierProof)
  have publicRouteStable : Cont verifierProof R publicRoute :=
    cont_result_hsame_transport publicVerifier (hsame_refl publicRoute)
  exact
    {
      core := {
        carrier_inhabited :=
          Exists.intro publicRoute
            (And.intro (hsame_refl publicRoute)
              (And.intro verifierRouteStable publicRouteStable))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          exact
            And.intro (hsame_trans (hsame_symm same) source.left)
              (And.intro source.right.left source.right.right)
      }
      pattern_sound := by
        intro row source
        exact And.intro source.left source.right.left
      ledger_sound := by
        intro row source
        exact And.intro source.left packageRoute
    }

end BEDC.Derived.LargeModelOutputVerifierUp
