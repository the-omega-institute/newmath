import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProofTraceAuditWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProofTraceAuditWitnessUp : Type where
  | mk :
      (trace source classifier transport ledger forbidden verdict provenance name : BHist) →
      ProofTraceAuditWitnessUp
  deriving DecidableEq

def proofTraceAuditWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proofTraceAuditWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proofTraceAuditWitnessEncodeBHist h

def proofTraceAuditWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proofTraceAuditWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proofTraceAuditWitnessDecodeBHist tail)

private theorem proofTraceAuditWitness_decode_encode_bhist :
    ∀ h : BHist,
      proofTraceAuditWitnessDecodeBHist (proofTraceAuditWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def proofTraceAuditWitnessFields : ProofTraceAuditWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProofTraceAuditWitnessUp.mk trace source classifier transport ledger forbidden verdict
      provenance name =>
      [trace, source, classifier, transport, ledger, forbidden, verdict, provenance, name]

def proofTraceAuditWitnessToEventFlow : ProofTraceAuditWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProofTraceAuditWitnessUp.mk trace source classifier transport ledger forbidden verdict
      provenance name =>
      [[BMark.b0],
        proofTraceAuditWitnessEncodeBHist trace,
        [BMark.b1, BMark.b0],
        proofTraceAuditWitnessEncodeBHist source,
        [BMark.b1, BMark.b1, BMark.b0],
        proofTraceAuditWitnessEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTraceAuditWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTraceAuditWitnessEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTraceAuditWitnessEncodeBHist forbidden,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofTraceAuditWitnessEncodeBHist verdict,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        proofTraceAuditWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        proofTraceAuditWitnessEncodeBHist name]

def proofTraceAuditWitnessFromEventFlow :
    EventFlow → Option ProofTraceAuditWitnessUp
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
              | source :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | ledger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | forbidden :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | verdict :: rest13 =>
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
                                                                                (ProofTraceAuditWitnessUp.mk
                                                                                  (proofTraceAuditWitnessDecodeBHist
                                                                                    trace)
                                                                                  (proofTraceAuditWitnessDecodeBHist
                                                                                    source)
                                                                                  (proofTraceAuditWitnessDecodeBHist
                                                                                    classifier)
                                                                                  (proofTraceAuditWitnessDecodeBHist
                                                                                    transport)
                                                                                  (proofTraceAuditWitnessDecodeBHist
                                                                                    ledger)
                                                                                  (proofTraceAuditWitnessDecodeBHist
                                                                                    forbidden)
                                                                                  (proofTraceAuditWitnessDecodeBHist
                                                                                    verdict)
                                                                                  (proofTraceAuditWitnessDecodeBHist
                                                                                    provenance)
                                                                                  (proofTraceAuditWitnessDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem proofTraceAuditWitness_round_trip :
    ∀ x : ProofTraceAuditWitnessUp,
      proofTraceAuditWitnessFromEventFlow (proofTraceAuditWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk trace source classifier transport ledger forbidden verdict provenance name =>
      change
        some
          (ProofTraceAuditWitnessUp.mk
            (proofTraceAuditWitnessDecodeBHist (proofTraceAuditWitnessEncodeBHist trace))
            (proofTraceAuditWitnessDecodeBHist (proofTraceAuditWitnessEncodeBHist source))
            (proofTraceAuditWitnessDecodeBHist
              (proofTraceAuditWitnessEncodeBHist classifier))
            (proofTraceAuditWitnessDecodeBHist
              (proofTraceAuditWitnessEncodeBHist transport))
            (proofTraceAuditWitnessDecodeBHist (proofTraceAuditWitnessEncodeBHist ledger))
            (proofTraceAuditWitnessDecodeBHist
              (proofTraceAuditWitnessEncodeBHist forbidden))
            (proofTraceAuditWitnessDecodeBHist (proofTraceAuditWitnessEncodeBHist verdict))
            (proofTraceAuditWitnessDecodeBHist
              (proofTraceAuditWitnessEncodeBHist provenance))
            (proofTraceAuditWitnessDecodeBHist (proofTraceAuditWitnessEncodeBHist name))) =
          some
            (ProofTraceAuditWitnessUp.mk trace source classifier transport ledger forbidden
              verdict provenance name)
      rw [proofTraceAuditWitness_decode_encode_bhist trace,
        proofTraceAuditWitness_decode_encode_bhist source,
        proofTraceAuditWitness_decode_encode_bhist classifier,
        proofTraceAuditWitness_decode_encode_bhist transport,
        proofTraceAuditWitness_decode_encode_bhist ledger,
        proofTraceAuditWitness_decode_encode_bhist forbidden,
        proofTraceAuditWitness_decode_encode_bhist verdict,
        proofTraceAuditWitness_decode_encode_bhist provenance,
        proofTraceAuditWitness_decode_encode_bhist name]

private theorem proofTraceAuditWitnessToEventFlow_injective
    {x y : ProofTraceAuditWitnessUp} :
    proofTraceAuditWitnessToEventFlow x = proofTraceAuditWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proofTraceAuditWitnessFromEventFlow (proofTraceAuditWitnessToEventFlow x) =
        proofTraceAuditWitnessFromEventFlow (proofTraceAuditWitnessToEventFlow y) :=
    congrArg proofTraceAuditWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (proofTraceAuditWitness_round_trip x).symm
      (Eq.trans hread (proofTraceAuditWitness_round_trip y)))

private theorem proofTraceAuditWitness_field_faithful :
    ∀ x y : ProofTraceAuditWitnessUp,
      proofTraceAuditWitnessFields x = proofTraceAuditWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk trace source classifier transport ledger forbidden verdict provenance name =>
      cases y with
      | mk trace' source' classifier' transport' ledger' forbidden' verdict' provenance'
          name' =>
          cases hfields
          rfl

instance proofTraceAuditWitnessBHistCarrier : BHistCarrier ProofTraceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proofTraceAuditWitnessToEventFlow
  fromEventFlow := proofTraceAuditWitnessFromEventFlow

instance proofTraceAuditWitnessChapterTasteGate :
    ChapterTasteGate ProofTraceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proofTraceAuditWitnessFromEventFlow (proofTraceAuditWitnessToEventFlow x) = some x
    exact proofTraceAuditWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (proofTraceAuditWitnessToEventFlow_injective heq)

instance proofTraceAuditWitnessFieldFaithful : FieldFaithful ProofTraceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := proofTraceAuditWitnessFields
  field_faithful := proofTraceAuditWitness_field_faithful

instance proofTraceAuditWitnessNontrivial : Nontrivial ProofTraceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProofTraceAuditWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProofTraceAuditWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProofTraceAuditWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  proofTraceAuditWitnessChapterTasteGate

theorem ProofTraceAuditWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      proofTraceAuditWitnessDecodeBHist (proofTraceAuditWitnessEncodeBHist h) = h) ∧
      (∀ x : ProofTraceAuditWitnessUp,
        proofTraceAuditWitnessFromEventFlow (proofTraceAuditWitnessToEventFlow x) = some x) ∧
        (∀ x y : ProofTraceAuditWitnessUp,
          proofTraceAuditWitnessToEventFlow x = proofTraceAuditWitnessToEventFlow y →
            x = y) ∧
          Nonempty (Nontrivial ProofTraceAuditWitnessUp) ∧
            Nonempty (ChapterTasteGate ProofTraceAuditWitnessUp) ∧
              Nonempty (FieldFaithful ProofTraceAuditWitnessUp) ∧
                proofTraceAuditWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact proofTraceAuditWitness_decode_encode_bhist
  · constructor
    · exact proofTraceAuditWitness_round_trip
    · constructor
      · intro x y heq
        exact proofTraceAuditWitnessToEventFlow_injective heq
      · constructor
        · exact ⟨proofTraceAuditWitnessNontrivial⟩
        · constructor
          · exact ⟨proofTraceAuditWitnessChapterTasteGate⟩
          · constructor
            · exact ⟨proofTraceAuditWitnessFieldFaithful⟩
            · rfl

theorem ProofTraceAuditWitnessNameCertObligations
    (trace source classifier transport ledger forbidden verdict provenance name : BHist) :
    proofTraceAuditWitnessFields
        (ProofTraceAuditWitnessUp.mk trace source classifier transport ledger forbidden verdict
          provenance name) =
      [trace, source, classifier, transport, ledger, forbidden, verdict, provenance, name] ∧
      hsame (append transport ledger) (append transport ledger) ∧
        Cont trace source (append trace source) ∧
          Cont transport ledger (append transport ledger) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · rfl
  · constructor
    · exact hsame_refl (append transport ledger)
    · constructor
      · rfl
      · rfl

end BEDC.Derived.ProofTraceAuditWitnessUp
