import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProofPatternClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProofPatternClassifierUp : Type where
  | mk (W L D R E G H C Q N : BHist) : ProofPatternClassifierUp
  deriving DecidableEq

def proofPatternClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proofPatternClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proofPatternClassifierEncodeBHist h

def proofPatternClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proofPatternClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proofPatternClassifierDecodeBHist tail)

private theorem proofPatternClassifierDecode_encode_bhist :
    ∀ h : BHist, proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def proofPatternClassifierToEventFlow : ProofPatternClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProofPatternClassifierUp.mk W L D R E G H C Q N =>
      [[BMark.b0],
        proofPatternClassifierEncodeBHist W,
        [BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        proofPatternClassifierEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        proofPatternClassifierEncodeBHist N]

def proofPatternClassifierFromEventFlow : EventFlow → Option ProofPatternClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | G :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | Q :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ProofPatternClassifierUp.mk
                                                                                          (proofPatternClassifierDecodeBHist W)
                                                                                          (proofPatternClassifierDecodeBHist L)
                                                                                          (proofPatternClassifierDecodeBHist D)
                                                                                          (proofPatternClassifierDecodeBHist R)
                                                                                          (proofPatternClassifierDecodeBHist E)
                                                                                          (proofPatternClassifierDecodeBHist G)
                                                                                          (proofPatternClassifierDecodeBHist H)
                                                                                          (proofPatternClassifierDecodeBHist C)
                                                                                          (proofPatternClassifierDecodeBHist Q)
                                                                                          (proofPatternClassifierDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem proofPatternClassifier_round_trip :
    ∀ x : ProofPatternClassifierUp,
      proofPatternClassifierFromEventFlow (proofPatternClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W L D R E G H C Q N =>
      change
        some
          (ProofPatternClassifierUp.mk
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist W))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist L))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist D))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist R))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist E))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist G))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist H))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist C))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist Q))
            (proofPatternClassifierDecodeBHist (proofPatternClassifierEncodeBHist N))) =
          some (ProofPatternClassifierUp.mk W L D R E G H C Q N)
      rw [proofPatternClassifierDecode_encode_bhist W,
        proofPatternClassifierDecode_encode_bhist L,
        proofPatternClassifierDecode_encode_bhist D,
        proofPatternClassifierDecode_encode_bhist R,
        proofPatternClassifierDecode_encode_bhist E,
        proofPatternClassifierDecode_encode_bhist G,
        proofPatternClassifierDecode_encode_bhist H,
        proofPatternClassifierDecode_encode_bhist C,
        proofPatternClassifierDecode_encode_bhist Q,
        proofPatternClassifierDecode_encode_bhist N]

private theorem proofPatternClassifierToEventFlow_injective {x y : ProofPatternClassifierUp} :
    proofPatternClassifierToEventFlow x = proofPatternClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proofPatternClassifierFromEventFlow (proofPatternClassifierToEventFlow x) =
        proofPatternClassifierFromEventFlow (proofPatternClassifierToEventFlow y) :=
    congrArg proofPatternClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (proofPatternClassifier_round_trip x).symm
      (Eq.trans hread (proofPatternClassifier_round_trip y)))

instance proofPatternClassifierBHistCarrier : BHistCarrier ProofPatternClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proofPatternClassifierToEventFlow
  fromEventFlow := proofPatternClassifierFromEventFlow

instance proofPatternClassifierChapterTasteGate : ChapterTasteGate ProofPatternClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proofPatternClassifierFromEventFlow (proofPatternClassifierToEventFlow x) = some x
    exact proofPatternClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (proofPatternClassifierToEventFlow_injective heq)

instance proofPatternClassifierFieldFaithful : FieldFaithful ProofPatternClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ProofPatternClassifierUp.mk W L D R E G H C Q N => [W, L, D, R, E, G, H, C, Q, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk W₁ L₁ D₁ R₁ E₁ G₁ H₁ C₁ Q₁ N₁ =>
        cases y with
        | mk W₂ L₂ D₂ R₂ E₂ G₂ H₂ C₂ Q₂ N₂ =>
            simp only [] at h
            cases h
            rfl

instance proofPatternClassifierNontrivial : Nontrivial ProofPatternClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProofPatternClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProofPatternClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProofPatternClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  proofPatternClassifierChapterTasteGate

end BEDC.Derived.ProofPatternClassifierUp
