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

def largeModelOutputVerifierFromEventFlow : EventFlow → Option LargeModelOutputVerifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [[BMark.b0], harness, [BMark.b1, BMark.b0], auditChannel,
      [BMark.b1, BMark.b1, BMark.b0], modelTrace,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b0], promptResponse,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], inscriptionAudit,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], verifier,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
      proofCheck,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b0],
      refusal,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b0],
      route,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b1, BMark.b0],
      replay,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b1, BMark.b1, BMark.b0],
      provenance,
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
      localName] =>
      some
        (LargeModelOutputVerifierUp.mk
          (largeModelOutputVerifierDecodeBHist harness)
          (largeModelOutputVerifierDecodeBHist auditChannel)
          (largeModelOutputVerifierDecodeBHist modelTrace)
          (largeModelOutputVerifierDecodeBHist promptResponse)
          (largeModelOutputVerifierDecodeBHist inscriptionAudit)
          (largeModelOutputVerifierDecodeBHist verifier)
          (largeModelOutputVerifierDecodeBHist proofCheck)
          (largeModelOutputVerifierDecodeBHist refusal)
          (largeModelOutputVerifierDecodeBHist route)
          (largeModelOutputVerifierDecodeBHist replay)
          (largeModelOutputVerifierDecodeBHist provenance)
          (largeModelOutputVerifierDecodeBHist localName))
  | _ => none

private theorem largeModelOutputVerifier_round_trip :
    ∀ x : LargeModelOutputVerifierUp,
      largeModelOutputVerifierFromEventFlow (largeModelOutputVerifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk harness auditChannel modelTrace promptResponse inscriptionAudit verifier proofCheck
      refusal route replay provenance localName =>
      simp only [largeModelOutputVerifierToEventFlow, largeModelOutputVerifierFromEventFlow,
        largeModelOutputVerifierDecode_encode_bhist]

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

instance largeModelOutputVerifierChapterTasteGate :
    ChapterTasteGate LargeModelOutputVerifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change largeModelOutputVerifierFromEventFlow (largeModelOutputVerifierToEventFlow x) =
      some x
    exact largeModelOutputVerifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelOutputVerifierToEventFlow_injective heq)

instance largeModelOutputVerifierFieldFaithful : FieldFaithful LargeModelOutputVerifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LargeModelOutputVerifierUp.mk harness auditChannel modelTrace promptResponse
        inscriptionAudit verifier proofCheck refusal route replay provenance localName =>
        [harness, auditChannel, modelTrace, promptResponse, inscriptionAudit, verifier,
          proofCheck, refusal, route, replay, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk harness1 auditChannel1 modelTrace1 promptResponse1 inscriptionAudit1 verifier1
        proofCheck1 refusal1 route1 replay1 provenance1 localName1 =>
        cases y with
        | mk harness2 auditChannel2 modelTrace2 promptResponse2 inscriptionAudit2 verifier2
            proofCheck2 refusal2 route2 replay2 provenance2 localName2 =>
            cases h
            rfl

instance largeModelOutputVerifierNontrivial : Nontrivial LargeModelOutputVerifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LargeModelOutputVerifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
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
      largeModelOutputVerifierDecodeBHist (largeModelOutputVerifierEncodeBHist h) = h) ∧
      (forall x : LargeModelOutputVerifierUp,
        largeModelOutputVerifierFromEventFlow (largeModelOutputVerifierToEventFlow x) = some x) ∧
        (forall x y : LargeModelOutputVerifierUp,
          largeModelOutputVerifierToEventFlow x = largeModelOutputVerifierToEventFlow y -> x = y) ∧
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
