import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationReflectionHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.MainTheorems
open BEDC.Meta.TasteGate

inductive ObservationReflectionHandoffUp : Type where
  | mk : (O S R B L K C T M E P N : BHist) → ObservationReflectionHandoffUp
  deriving DecidableEq

private def observationReflectionHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationReflectionHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationReflectionHandoffEncodeBHist h

private def observationReflectionHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationReflectionHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationReflectionHandoffDecodeBHist tail)

private theorem observationReflectionHandoffDecode_encode_bhist :
    ∀ h : BHist,
      observationReflectionHandoffDecodeBHist
        (observationReflectionHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def observationReflectionHandoffToEventFlow :
    ObservationReflectionHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationReflectionHandoffUp.mk O S R B L K C T M E P N =>
      [[BMark.b0],
        observationReflectionHandoffEncodeBHist O,
        [BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observationReflectionHandoffEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationReflectionHandoffEncodeBHist N]

private def observationReflectionHandoffFromEventFlow :
    EventFlow → Option ObservationReflectionHandoffUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | O :: rest1 =>
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
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | B :: rest7 =>
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
                                              | K :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | T :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | M :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | E :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | P :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | N :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (ObservationReflectionHandoffUp.mk
                                                                                                          (observationReflectionHandoffDecodeBHist O)
                                                                                                          (observationReflectionHandoffDecodeBHist S)
                                                                                                          (observationReflectionHandoffDecodeBHist R)
                                                                                                          (observationReflectionHandoffDecodeBHist B)
                                                                                                          (observationReflectionHandoffDecodeBHist L)
                                                                                                          (observationReflectionHandoffDecodeBHist K)
                                                                                                          (observationReflectionHandoffDecodeBHist C)
                                                                                                          (observationReflectionHandoffDecodeBHist T)
                                                                                                          (observationReflectionHandoffDecodeBHist M)
                                                                                                          (observationReflectionHandoffDecodeBHist E)
                                                                                                          (observationReflectionHandoffDecodeBHist P)
                                                                                                          (observationReflectionHandoffDecodeBHist N))
                                                                                                  | _ :: _ => none

theorem ObservationReflectionHandoffUp_taste_gate_boundary_mk_congr
    {O O' S S' R R' B B' L L' K K' C C' T T' M M' E E' P P' N N' : BHist}
    (hO : O' = O)
    (hS : S' = S)
    (hR : R' = R)
    (hB : B' = B)
    (hL : L' = L)
    (hK : K' = K)
    (hC : C' = C)
    (hT : T' = T)
    (hM : M' = M)
    (hE : E' = E)
    (hP : P' = P)
    (hN : N' = N) :
    ObservationReflectionHandoffUp.mk O' S' R' B' L' K' C' T' M' E' P' N' =
      ObservationReflectionHandoffUp.mk O S R B L K C T M E P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hO
  cases hS
  cases hR
  cases hB
  cases hL
  cases hK
  cases hC
  cases hT
  cases hM
  cases hE
  cases hP
  cases hN
  rfl

theorem ObservationReflectionHandoffUp_taste_gate_boundary_round_trip :
    ∀ x : ObservationReflectionHandoffUp,
      observationReflectionHandoffFromEventFlow
        (observationReflectionHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O S R B L K C T M E P N =>
      change
        some
          (ObservationReflectionHandoffUp.mk
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist O))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist S))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist R))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist B))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist L))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist K))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist C))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist T))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist M))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist E))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist P))
            (observationReflectionHandoffDecodeBHist
              (observationReflectionHandoffEncodeBHist N))) =
          some (ObservationReflectionHandoffUp.mk O S R B L K C T M E P N)
      have hO := observationReflectionHandoffDecode_encode_bhist O
      have hS := observationReflectionHandoffDecode_encode_bhist S
      have hR := observationReflectionHandoffDecode_encode_bhist R
      have hB := observationReflectionHandoffDecode_encode_bhist B
      have hL := observationReflectionHandoffDecode_encode_bhist L
      have hK := observationReflectionHandoffDecode_encode_bhist K
      have hC := observationReflectionHandoffDecode_encode_bhist C
      have hT := observationReflectionHandoffDecode_encode_bhist T
      have hM := observationReflectionHandoffDecode_encode_bhist M
      have hE := observationReflectionHandoffDecode_encode_bhist E
      have hP := observationReflectionHandoffDecode_encode_bhist P
      have hN := observationReflectionHandoffDecode_encode_bhist N
      exact congrArg some
        (ObservationReflectionHandoffUp_taste_gate_boundary_mk_congr hO hS hR hB hL hK hC hT
          hM hE hP hN)

private theorem observationReflectionHandoffToEventFlow_injective
    {x y : ObservationReflectionHandoffUp} :
    observationReflectionHandoffToEventFlow x =
      observationReflectionHandoffToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observationReflectionHandoffFromEventFlow
          (observationReflectionHandoffToEventFlow x) =
        observationReflectionHandoffFromEventFlow
          (observationReflectionHandoffToEventFlow y) :=
    congrArg observationReflectionHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ObservationReflectionHandoffUp_taste_gate_boundary_round_trip x).symm
      (Eq.trans hread (ObservationReflectionHandoffUp_taste_gate_boundary_round_trip y)))

instance observationReflectionHandoffBHistCarrier :
    BHistCarrier ObservationReflectionHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observationReflectionHandoffToEventFlow
  fromEventFlow := observationReflectionHandoffFromEventFlow

instance observationReflectionHandoffChapterTasteGate :
    ChapterTasteGate ObservationReflectionHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observationReflectionHandoffFromEventFlow
        (observationReflectionHandoffToEventFlow x) = some x
    exact ObservationReflectionHandoffUp_taste_gate_boundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationReflectionHandoffToEventFlow_injective heq)

instance observationReflectionHandoffFieldFaithful :
    FieldFaithful ObservationReflectionHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObservationReflectionHandoffUp.mk O S R B L K C T M E P N =>
        [O, S, R, B, L, K, C, T, M, E, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk O₁ S₁ R₁ B₁ L₁ K₁ C₁ T₁ M₁ E₁ P₁ N₁ =>
        cases y with
        | mk O₂ S₂ R₂ B₂ L₂ K₂ C₂ T₂ M₂ E₂ P₂ N₂ =>
            cases h
            rfl

instance observationReflectionHandoffNontrivial :
    Nontrivial ObservationReflectionHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObservationReflectionHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ObservationReflectionHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObservationReflectionHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observationReflectionHandoffChapterTasteGate

theorem ObservationReflectionHandoffUp_taste_gate_boundary :
    (∀ x : ObservationReflectionHandoffUp,
      ∃ e : EventFlow, observationReflectionHandoffFromEventFlow e = some x) ∧
      (∀ (x : ObservationReflectionHandoffUp) (w : RawEvent) (m : BMark),
        List.Mem w (observationReflectionHandoffToEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  constructor
  · intro x
    exact ⟨observationReflectionHandoffToEventFlow x,
      ObservationReflectionHandoffUp_taste_gate_boundary_round_trip x⟩
  · intro x w m hw hm
    exact BMark_generated_cases m

end BEDC.Derived.ObservationReflectionHandoffUp
