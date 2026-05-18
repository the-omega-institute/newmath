import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TraceVerdictBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TraceVerdictBoundaryUp : Type where
  | mk :
      (trace refusal verdict interfaceTarget proofSite transport continuation provenance
        name : BHist) →
      TraceVerdictBoundaryUp
  deriving DecidableEq

def traceVerdictBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: traceVerdictBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: traceVerdictBoundaryEncodeBHist h

def traceVerdictBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (traceVerdictBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (traceVerdictBoundaryDecodeBHist tail)

private theorem traceVerdictBoundary_decode_encode_bhist :
    ∀ h : BHist,
      traceVerdictBoundaryDecodeBHist (traceVerdictBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def traceVerdictBoundaryFields : TraceVerdictBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TraceVerdictBoundaryUp.mk trace refusal verdict interfaceTarget proofSite transport
      continuation provenance name =>
      [trace, refusal, verdict, interfaceTarget, proofSite, transport, continuation,
        provenance, name]

def traceVerdictBoundaryToEventFlow : TraceVerdictBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TraceVerdictBoundaryUp.mk trace refusal verdict interfaceTarget proofSite transport
      continuation provenance name =>
      [[BMark.b0],
        traceVerdictBoundaryEncodeBHist trace,
        [BMark.b1, BMark.b0],
        traceVerdictBoundaryEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b0],
        traceVerdictBoundaryEncodeBHist verdict,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        traceVerdictBoundaryEncodeBHist interfaceTarget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        traceVerdictBoundaryEncodeBHist proofSite,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        traceVerdictBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        traceVerdictBoundaryEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        traceVerdictBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        traceVerdictBoundaryEncodeBHist name]

def traceVerdictBoundaryFromEventFlow :
    EventFlow → Option TraceVerdictBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | trace :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | refusal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | verdict :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | interfaceTarget :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | proofSite :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (TraceVerdictBoundaryUp.mk
                                                                                  (traceVerdictBoundaryDecodeBHist
                                                                                    trace)
                                                                                  (traceVerdictBoundaryDecodeBHist
                                                                                    refusal)
                                                                                  (traceVerdictBoundaryDecodeBHist
                                                                                    verdict)
                                                                                  (traceVerdictBoundaryDecodeBHist
                                                                                    interfaceTarget)
                                                                                  (traceVerdictBoundaryDecodeBHist
                                                                                    proofSite)
                                                                                  (traceVerdictBoundaryDecodeBHist
                                                                                    transport)
                                                                                  (traceVerdictBoundaryDecodeBHist
                                                                                    continuation)
                                                                                  (traceVerdictBoundaryDecodeBHist
                                                                                    provenance)
                                                                                  (traceVerdictBoundaryDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem traceVerdictBoundary_round_trip :
    ∀ x : TraceVerdictBoundaryUp,
      traceVerdictBoundaryFromEventFlow (traceVerdictBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk trace refusal verdict interfaceTarget proofSite transport continuation provenance name =>
      change
        some
          (TraceVerdictBoundaryUp.mk
            (traceVerdictBoundaryDecodeBHist (traceVerdictBoundaryEncodeBHist trace))
            (traceVerdictBoundaryDecodeBHist (traceVerdictBoundaryEncodeBHist refusal))
            (traceVerdictBoundaryDecodeBHist (traceVerdictBoundaryEncodeBHist verdict))
            (traceVerdictBoundaryDecodeBHist
              (traceVerdictBoundaryEncodeBHist interfaceTarget))
            (traceVerdictBoundaryDecodeBHist (traceVerdictBoundaryEncodeBHist proofSite))
            (traceVerdictBoundaryDecodeBHist (traceVerdictBoundaryEncodeBHist transport))
            (traceVerdictBoundaryDecodeBHist
              (traceVerdictBoundaryEncodeBHist continuation))
            (traceVerdictBoundaryDecodeBHist
              (traceVerdictBoundaryEncodeBHist provenance))
            (traceVerdictBoundaryDecodeBHist (traceVerdictBoundaryEncodeBHist name))) =
          some
            (TraceVerdictBoundaryUp.mk trace refusal verdict interfaceTarget proofSite
              transport continuation provenance name)
      rw [traceVerdictBoundary_decode_encode_bhist trace,
        traceVerdictBoundary_decode_encode_bhist refusal,
        traceVerdictBoundary_decode_encode_bhist verdict,
        traceVerdictBoundary_decode_encode_bhist interfaceTarget,
        traceVerdictBoundary_decode_encode_bhist proofSite,
        traceVerdictBoundary_decode_encode_bhist transport,
        traceVerdictBoundary_decode_encode_bhist continuation,
        traceVerdictBoundary_decode_encode_bhist provenance,
        traceVerdictBoundary_decode_encode_bhist name]

private theorem traceVerdictBoundaryToEventFlow_injective
    {x y : TraceVerdictBoundaryUp} :
    traceVerdictBoundaryToEventFlow x = traceVerdictBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      traceVerdictBoundaryFromEventFlow (traceVerdictBoundaryToEventFlow x) =
        traceVerdictBoundaryFromEventFlow (traceVerdictBoundaryToEventFlow y) :=
    congrArg traceVerdictBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (traceVerdictBoundary_round_trip x).symm
      (Eq.trans hread (traceVerdictBoundary_round_trip y)))

private theorem traceVerdictBoundary_field_faithful :
    ∀ x y : TraceVerdictBoundaryUp,
      traceVerdictBoundaryFields x = traceVerdictBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk trace refusal verdict interfaceTarget proofSite transport continuation provenance name =>
      cases y with
      | mk trace' refusal' verdict' interfaceTarget' proofSite' transport' continuation'
          provenance' name' =>
          cases hfields
          rfl

instance traceVerdictBoundaryBHistCarrier : BHistCarrier TraceVerdictBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := traceVerdictBoundaryToEventFlow
  fromEventFlow := traceVerdictBoundaryFromEventFlow

instance traceVerdictBoundaryChapterTasteGate :
    ChapterTasteGate TraceVerdictBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change traceVerdictBoundaryFromEventFlow (traceVerdictBoundaryToEventFlow x) = some x
    exact traceVerdictBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (traceVerdictBoundaryToEventFlow_injective heq)

instance traceVerdictBoundaryFieldFaithful : FieldFaithful TraceVerdictBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := traceVerdictBoundaryFields
  field_faithful := traceVerdictBoundary_field_faithful

instance traceVerdictBoundaryNontrivial : Nontrivial TraceVerdictBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TraceVerdictBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TraceVerdictBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TraceVerdictBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

namespace TasteGate

theorem TraceVerdictBoundaryNameCertObligations
    (trace refusal verdict interfaceTarget proofSite transport continuation provenance
      name : BHist) :
    traceVerdictBoundaryFields
        (TraceVerdictBoundaryUp.mk trace refusal verdict interfaceTarget proofSite transport
          continuation provenance name) =
      [trace, refusal, verdict, interfaceTarget, proofSite, transport, continuation,
        provenance, name] ∧
      Cont trace refusal (append trace refusal) ∧
        Cont verdict interfaceTarget (append verdict interfaceTarget) ∧
          hsame (append verdict interfaceTarget) (append verdict interfaceTarget) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · exact hsame_refl (append verdict interfaceTarget)

end TasteGate

end BEDC.Derived.TraceVerdictBoundaryUp
