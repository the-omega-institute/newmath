import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationLogicBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationLogicBoundaryUp : Type where
  | mk : (O L M K G R H C P N : BHist) → ObservationLogicBoundaryUp
  deriving DecidableEq

def observationLogicBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationLogicBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationLogicBoundaryEncodeBHist h

def observationLogicBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationLogicBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationLogicBoundaryDecodeBHist tail)

private theorem observationLogicBoundary_decode_encode_bhist :
    ∀ h : BHist,
      observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observationLogicBoundaryFields : ObservationLogicBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationLogicBoundaryUp.mk O L M K G R H C P N => [O, L, M, K, G, R, H, C, P, N]

def observationLogicBoundaryToEventFlow : ObservationLogicBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationLogicBoundaryUp.mk O L M K G R H C P N =>
      [[BMark.b0],
        observationLogicBoundaryEncodeBHist O,
        [BMark.b1, BMark.b0],
        observationLogicBoundaryEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b0],
        observationLogicBoundaryEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationLogicBoundaryEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationLogicBoundaryEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationLogicBoundaryEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationLogicBoundaryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observationLogicBoundaryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observationLogicBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observationLogicBoundaryEncodeBHist N]

def observationLogicBoundaryFromEventFlow : EventFlow → Option ObservationLogicBoundaryUp
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
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | M :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | K :: rest7 =>
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
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ObservationLogicBoundaryUp.mk
                                                                                          (observationLogicBoundaryDecodeBHist O)
                                                                                          (observationLogicBoundaryDecodeBHist L)
                                                                                          (observationLogicBoundaryDecodeBHist M)
                                                                                          (observationLogicBoundaryDecodeBHist K)
                                                                                          (observationLogicBoundaryDecodeBHist G)
                                                                                          (observationLogicBoundaryDecodeBHist R)
                                                                                          (observationLogicBoundaryDecodeBHist H)
                                                                                          (observationLogicBoundaryDecodeBHist C)
                                                                                          (observationLogicBoundaryDecodeBHist P)
                                                                                          (observationLogicBoundaryDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem observationLogicBoundary_round_trip :
    ∀ x : ObservationLogicBoundaryUp,
      observationLogicBoundaryFromEventFlow (observationLogicBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O L M K G R H C P N =>
      change
        some
          (ObservationLogicBoundaryUp.mk
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist O))
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist L))
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist M))
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist K))
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist G))
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist R))
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist H))
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist C))
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist P))
            (observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist N))) =
          some (ObservationLogicBoundaryUp.mk O L M K G R H C P N)
      rw [observationLogicBoundary_decode_encode_bhist O,
        observationLogicBoundary_decode_encode_bhist L,
        observationLogicBoundary_decode_encode_bhist M,
        observationLogicBoundary_decode_encode_bhist K,
        observationLogicBoundary_decode_encode_bhist G,
        observationLogicBoundary_decode_encode_bhist R,
        observationLogicBoundary_decode_encode_bhist H,
        observationLogicBoundary_decode_encode_bhist C,
        observationLogicBoundary_decode_encode_bhist P,
        observationLogicBoundary_decode_encode_bhist N]

private theorem observationLogicBoundaryToEventFlow_injective
    {x y : ObservationLogicBoundaryUp} :
    observationLogicBoundaryToEventFlow x = observationLogicBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observationLogicBoundaryFromEventFlow (observationLogicBoundaryToEventFlow x) =
        observationLogicBoundaryFromEventFlow (observationLogicBoundaryToEventFlow y) :=
    congrArg observationLogicBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationLogicBoundary_round_trip x).symm
      (Eq.trans hread (observationLogicBoundary_round_trip y)))

private theorem observationLogicBoundary_field_faithful :
    ∀ x y : ObservationLogicBoundaryUp,
      observationLogicBoundaryFields x = observationLogicBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ L₁ M₁ K₁ G₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ L₂ M₂ K₂ G₂ R₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hO t1
          injection t1 with hL t2
          injection t2 with hM t3
          injection t3 with hK t4
          injection t4 with hG t5
          injection t5 with hR t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          cases hO
          cases hL
          cases hM
          cases hK
          cases hG
          cases hR
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance observationLogicBoundaryBHistCarrier : BHistCarrier ObservationLogicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observationLogicBoundaryToEventFlow
  fromEventFlow := observationLogicBoundaryFromEventFlow

instance observationLogicBoundaryChapterTasteGate :
    ChapterTasteGate ObservationLogicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observationLogicBoundaryFromEventFlow (observationLogicBoundaryToEventFlow x) = some x
    exact observationLogicBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationLogicBoundaryToEventFlow_injective heq)

instance observationLogicBoundaryFieldFaithful : FieldFaithful ObservationLogicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observationLogicBoundaryFields
  field_faithful := observationLogicBoundary_field_faithful

instance observationLogicBoundaryNontrivial : Nontrivial ObservationLogicBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObservationLogicBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObservationLogicBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObservationLogicBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observationLogicBoundaryChapterTasteGate

def taste_gate_witness : ChapterTasteGate ObservationLogicBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observationLogicBoundaryChapterTasteGate

theorem ObservationLogicBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ObservationLogicBoundaryUp) ∧
      Nonempty (FieldFaithful ObservationLogicBoundaryUp) ∧
        Nonempty (Nontrivial ObservationLogicBoundaryUp) ∧
          (∀ h : BHist,
            observationLogicBoundaryDecodeBHist (observationLogicBoundaryEncodeBHist h) = h) ∧
            (∀ x : ObservationLogicBoundaryUp,
              observationLogicBoundaryFromEventFlow (observationLogicBoundaryToEventFlow x) =
                some x) ∧
              (∀ x y : ObservationLogicBoundaryUp,
                observationLogicBoundaryToEventFlow x = observationLogicBoundaryToEventFlow y →
                  x = y) ∧
                observationLogicBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro observationLogicBoundaryChapterTasteGate,
      Nonempty.intro observationLogicBoundaryFieldFaithful,
      Nonempty.intro observationLogicBoundaryNontrivial,
      observationLogicBoundary_decode_encode_bhist,
      observationLogicBoundary_round_trip,
      (fun _ _ heq => observationLogicBoundaryToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ObservationLogicBoundaryUp
