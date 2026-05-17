import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProofWitnessChainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProofWitnessChainUp : Type where
  | mk
      (trace source classifier transport ledger refusal audit provenance name : BHist) :
      ProofWitnessChainUp
  deriving DecidableEq

private def encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def proofWitnessChainToEventFlow : ProofWitnessChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProofWitnessChainUp.mk trace source classifier transport ledger refusal audit provenance
      name =>
      [[BMark.b0],
        encodeBHist trace,
        [BMark.b1, BMark.b0],
        encodeBHist source,
        [BMark.b1, BMark.b1, BMark.b0],
        encodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        encodeBHist name]

private def proofWitnessChainFromEventFlow : EventFlow → Option ProofWitnessChainUp
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
                                              | refusal :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | audit :: rest13 =>
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
                                                                                (ProofWitnessChainUp.mk
                                                                                  (decodeBHist
                                                                                    trace)
                                                                                  (decodeBHist
                                                                                    source)
                                                                                  (decodeBHist
                                                                                    classifier)
                                                                                  (decodeBHist
                                                                                    transport)
                                                                                  (decodeBHist
                                                                                    ledger)
                                                                                  (decodeBHist
                                                                                    refusal)
                                                                                  (decodeBHist
                                                                                    audit)
                                                                                  (decodeBHist
                                                                                    provenance)
                                                                                  (decodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem proofWitnessChain_round_trip :
    ∀ x : ProofWitnessChainUp,
      proofWitnessChainFromEventFlow (proofWitnessChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk trace source classifier transport ledger refusal audit provenance name =>
      change
        some
          (ProofWitnessChainUp.mk
            (decodeBHist (encodeBHist trace)) (decodeBHist (encodeBHist source))
            (decodeBHist (encodeBHist classifier)) (decodeBHist (encodeBHist transport))
            (decodeBHist (encodeBHist ledger)) (decodeBHist (encodeBHist refusal))
            (decodeBHist (encodeBHist audit)) (decodeBHist (encodeBHist provenance))
            (decodeBHist (encodeBHist name))) =
          some
            (ProofWitnessChainUp.mk trace source classifier transport ledger refusal audit
              provenance name)
      rw [decode_encode_bhist trace, decode_encode_bhist source,
        decode_encode_bhist classifier, decode_encode_bhist transport,
        decode_encode_bhist ledger, decode_encode_bhist refusal, decode_encode_bhist audit,
        decode_encode_bhist provenance, decode_encode_bhist name]

private theorem proofWitnessChainToEventFlow_injective {x y : ProofWitnessChainUp} :
    proofWitnessChainToEventFlow x = proofWitnessChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proofWitnessChainFromEventFlow (proofWitnessChainToEventFlow x) =
        proofWitnessChainFromEventFlow (proofWitnessChainToEventFlow y) :=
    congrArg proofWitnessChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (proofWitnessChain_round_trip x).symm
      (Eq.trans hread (proofWitnessChain_round_trip y)))

instance proofWitnessChainBHistCarrier : BHistCarrier ProofWitnessChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proofWitnessChainToEventFlow
  fromEventFlow := proofWitnessChainFromEventFlow

instance proofWitnessChainChapterTasteGate : ChapterTasteGate ProofWitnessChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proofWitnessChainFromEventFlow (proofWitnessChainToEventFlow x) = some x
    exact proofWitnessChain_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (proofWitnessChainToEventFlow_injective heq)

instance proofWitnessChainFieldFaithful : FieldFaithful ProofWitnessChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ProofWitnessChainUp.mk trace source classifier transport ledger refusal audit provenance
        name =>
        [trace, source, classifier, transport, ledger, refusal, audit, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk trace₁ source₁ classifier₁ transport₁ ledger₁ refusal₁ audit₁ provenance₁ name₁ =>
        cases y with
        | mk trace₂ source₂ classifier₂ transport₂ ledger₂ refusal₂ audit₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance proofWitnessChainNontrivial : Nontrivial ProofWitnessChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProofWitnessChainUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProofWitnessChainUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProofWitnessChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  proofWitnessChainChapterTasteGate

end BEDC.Derived.ProofWitnessChainUp
