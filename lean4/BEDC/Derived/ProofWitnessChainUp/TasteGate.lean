import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProofWitnessChainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProofWitnessChainUp : Type where
  | mk (T S K H L F A P N : BHist) : ProofWitnessChainUp
  deriving DecidableEq

def proofWitnessChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proofWitnessChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proofWitnessChainEncodeBHist h

def proofWitnessChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proofWitnessChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proofWitnessChainDecodeBHist tail)

private theorem proofWitnessChain_decode_encode_bhist :
    ∀ h : BHist, proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def proofWitnessChainFields : ProofWitnessChainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProofWitnessChainUp.mk T S K H L F A P N => [T, S, K, H, L, F, A, P, N]

def proofWitnessChainToEventFlow : ProofWitnessChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProofWitnessChainUp.mk T S K H L F A P N =>
      [[BMark.b0],
        proofWitnessChainEncodeBHist T,
        [BMark.b1, BMark.b0],
        proofWitnessChainEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        proofWitnessChainEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofWitnessChainEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofWitnessChainEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofWitnessChainEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofWitnessChainEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        proofWitnessChainEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        proofWitnessChainEncodeBHist N]

def proofWitnessChainFromEventFlow : EventFlow → Option ProofWitnessChainUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | L :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | F :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | A :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ProofWitnessChainUp.mk
                                                                                  (proofWitnessChainDecodeBHist T)
                                                                                  (proofWitnessChainDecodeBHist S)
                                                                                  (proofWitnessChainDecodeBHist K)
                                                                                  (proofWitnessChainDecodeBHist H)
                                                                                  (proofWitnessChainDecodeBHist L)
                                                                                  (proofWitnessChainDecodeBHist F)
                                                                                  (proofWitnessChainDecodeBHist A)
                                                                                  (proofWitnessChainDecodeBHist P)
                                                                                  (proofWitnessChainDecodeBHist N))
                                                                          | _ :: _ => none

private theorem proofWitnessChain_round_trip :
    ∀ x : ProofWitnessChainUp,
      proofWitnessChainFromEventFlow (proofWitnessChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S K H L F A P N =>
      change
        some
          (ProofWitnessChainUp.mk
            (proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist T))
            (proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist S))
            (proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist K))
            (proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist H))
            (proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist L))
            (proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist F))
            (proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist A))
            (proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist P))
            (proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist N))) =
          some (ProofWitnessChainUp.mk T S K H L F A P N)
      rw [proofWitnessChain_decode_encode_bhist T,
        proofWitnessChain_decode_encode_bhist S,
        proofWitnessChain_decode_encode_bhist K,
        proofWitnessChain_decode_encode_bhist H,
        proofWitnessChain_decode_encode_bhist L,
        proofWitnessChain_decode_encode_bhist F,
        proofWitnessChain_decode_encode_bhist A,
        proofWitnessChain_decode_encode_bhist P,
        proofWitnessChain_decode_encode_bhist N]

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

private theorem proofWitnessChain_field_faithful :
    ∀ x y : ProofWitnessChainUp, proofWitnessChainFields x = proofWitnessChainFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T S K H L F A P N =>
      cases y with
      | mk T' S' K' H' L' F' A' P' N' =>
          cases hfields
          rfl

instance proofWitnessChainBHistCarrier : BHistCarrier ProofWitnessChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proofWitnessChainToEventFlow
  fromEventFlow := proofWitnessChainFromEventFlow

instance proofWitnessChainChapterTasteGate :
    ChapterTasteGate ProofWitnessChainUp where
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
  fields := proofWitnessChainFields
  field_faithful := proofWitnessChain_field_faithful

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

theorem ProofWitnessChainTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      proofWitnessChainDecodeBHist (proofWitnessChainEncodeBHist h) = h) ∧
      (∀ x : ProofWitnessChainUp,
        proofWitnessChainFromEventFlow (proofWitnessChainToEventFlow x) = some x) ∧
        (∀ x y : ProofWitnessChainUp,
          proofWitnessChainToEventFlow x = proofWitnessChainToEventFlow y → x = y) ∧
          Nonempty (Nontrivial ProofWitnessChainUp) ∧
            Nonempty (ChapterTasteGate ProofWitnessChainUp) ∧
              Nonempty (FieldFaithful ProofWitnessChainUp) ∧
                proofWitnessChainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact proofWitnessChain_decode_encode_bhist
  · constructor
    · exact proofWitnessChain_round_trip
    · constructor
      · intro x y heq
        exact proofWitnessChainToEventFlow_injective heq
      · constructor
        · exact ⟨proofWitnessChainNontrivial⟩
        · constructor
          · exact ⟨proofWitnessChainChapterTasteGate⟩
          · constructor
            · exact ⟨proofWitnessChainFieldFaithful⟩
            · rfl

end BEDC.Derived.ProofWitnessChainUp
