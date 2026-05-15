import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompilerTraceFaithfulnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompilerTraceFaithfulnessUp : Type where
  | mk : (S T K M G R L H C P N : BHist) → CompilerTraceFaithfulnessUp
  deriving DecidableEq

def compilerTraceFaithfulnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compilerTraceFaithfulnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compilerTraceFaithfulnessEncodeBHist h

def compilerTraceFaithfulnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compilerTraceFaithfulnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compilerTraceFaithfulnessDecodeBHist tail)

private theorem compilerTraceFaithfulnessDecode_encode_bhist :
    ∀ h : BHist,
      compilerTraceFaithfulnessDecodeBHist
        (compilerTraceFaithfulnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compilerTraceFaithfulnessToEventFlow :
    CompilerTraceFaithfulnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompilerTraceFaithfulnessUp.mk S T K M G R L H C P N =>
      [[BMark.b0],
        compilerTraceFaithfulnessEncodeBHist S,
        [BMark.b1, BMark.b0],
        compilerTraceFaithfulnessEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        compilerTraceFaithfulnessEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerTraceFaithfulnessEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerTraceFaithfulnessEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerTraceFaithfulnessEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerTraceFaithfulnessEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compilerTraceFaithfulnessEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compilerTraceFaithfulnessEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        compilerTraceFaithfulnessEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compilerTraceFaithfulnessEncodeBHist N]

def compilerTraceFaithfulnessFromEventFlow :
    EventFlow → Option CompilerTraceFaithfulnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
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
                              | M :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | G :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | L :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CompilerTraceFaithfulnessUp.mk
                                                                                                  (compilerTraceFaithfulnessDecodeBHist S)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist T)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist K)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist M)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist G)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist R)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist L)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist H)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist C)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist P)
                                                                                                  (compilerTraceFaithfulnessDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem compilerTraceFaithfulness_round_trip :
    ∀ x : CompilerTraceFaithfulnessUp,
      compilerTraceFaithfulnessFromEventFlow
        (compilerTraceFaithfulnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T K M G R L H C P N =>
      change
        some
          (CompilerTraceFaithfulnessUp.mk
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist S))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist T))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist K))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist M))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist G))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist R))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist L))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist H))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist C))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist P))
            (compilerTraceFaithfulnessDecodeBHist
              (compilerTraceFaithfulnessEncodeBHist N))) =
          some (CompilerTraceFaithfulnessUp.mk S T K M G R L H C P N)
      rw [compilerTraceFaithfulnessDecode_encode_bhist S,
        compilerTraceFaithfulnessDecode_encode_bhist T,
        compilerTraceFaithfulnessDecode_encode_bhist K,
        compilerTraceFaithfulnessDecode_encode_bhist M,
        compilerTraceFaithfulnessDecode_encode_bhist G,
        compilerTraceFaithfulnessDecode_encode_bhist R,
        compilerTraceFaithfulnessDecode_encode_bhist L,
        compilerTraceFaithfulnessDecode_encode_bhist H,
        compilerTraceFaithfulnessDecode_encode_bhist C,
        compilerTraceFaithfulnessDecode_encode_bhist P,
        compilerTraceFaithfulnessDecode_encode_bhist N]

private theorem compilerTraceFaithfulnessToEventFlow_injective
    {x y : CompilerTraceFaithfulnessUp} :
    compilerTraceFaithfulnessToEventFlow x =
      compilerTraceFaithfulnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compilerTraceFaithfulnessFromEventFlow
          (compilerTraceFaithfulnessToEventFlow x) =
        compilerTraceFaithfulnessFromEventFlow
          (compilerTraceFaithfulnessToEventFlow y) :=
    congrArg compilerTraceFaithfulnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compilerTraceFaithfulness_round_trip x).symm
      (Eq.trans hread (compilerTraceFaithfulness_round_trip y)))

instance compilerTraceFaithfulnessBHistCarrier :
    BHistCarrier CompilerTraceFaithfulnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compilerTraceFaithfulnessToEventFlow
  fromEventFlow := compilerTraceFaithfulnessFromEventFlow

instance compilerTraceFaithfulnessChapterTasteGate :
    ChapterTasteGate CompilerTraceFaithfulnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compilerTraceFaithfulnessFromEventFlow
        (compilerTraceFaithfulnessToEventFlow x) = some x
    exact compilerTraceFaithfulness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compilerTraceFaithfulnessToEventFlow_injective heq)

instance compilerTraceFaithfulnessFieldFaithful :
    FieldFaithful CompilerTraceFaithfulnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CompilerTraceFaithfulnessUp.mk S T K M G R L H C P N =>
        [S, T, K, M, G, R, L, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk S₁ T₁ K₁ M₁ G₁ R₁ L₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk S₂ T₂ K₂ M₂ G₂ R₂ L₂ H₂ C₂ P₂ N₂ =>
            injection h with hS t1
            injection t1 with hT t2
            injection t2 with hK t3
            injection t3 with hM t4
            injection t4 with hG t5
            injection t5 with hR t6
            injection t6 with hL t7
            injection t7 with hH t8
            injection t8 with hC t9
            injection t9 with hP t10
            injection t10 with hN _
            cases hS
            cases hT
            cases hK
            cases hM
            cases hG
            cases hR
            cases hL
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance compilerTraceFaithfulnessNontrivial :
    Nontrivial CompilerTraceFaithfulnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompilerTraceFaithfulnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompilerTraceFaithfulnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompilerTraceFaithfulnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem CompilerTraceFaithfulnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compilerTraceFaithfulnessDecodeBHist (compilerTraceFaithfulnessEncodeBHist h) = h) ∧
      (∀ x : CompilerTraceFaithfulnessUp,
        compilerTraceFaithfulnessFromEventFlow (compilerTraceFaithfulnessToEventFlow x) =
          some x) ∧
        (∀ x y : CompilerTraceFaithfulnessUp,
          compilerTraceFaithfulnessToEventFlow x =
            compilerTraceFaithfulnessToEventFlow y → x = y) ∧
          compilerTraceFaithfulnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compilerTraceFaithfulnessDecode_encode_bhist
  · constructor
    · exact compilerTraceFaithfulness_round_trip
    · constructor
      · intro x y heq
        exact compilerTraceFaithfulnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.CompilerTraceFaithfulnessUp
