import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReflectionGapBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReflectionGapBoundaryUp : Type where
  | mk (S H Sigma K P L Q T R N B : BHist) : ReflectionGapBoundaryUp
  deriving DecidableEq

def reflectionGapBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reflectionGapBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reflectionGapBoundaryEncodeBHist h

def reflectionGapBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reflectionGapBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reflectionGapBoundaryDecodeBHist tail)

private theorem reflectionGapBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def reflectionGapBoundaryFields : ReflectionGapBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ReflectionGapBoundaryUp.mk S H Sigma K P L Q T R N B =>
      [S, H, Sigma, K, P, L, Q, T, R, N, B]

def reflectionGapBoundaryToEventFlow : ReflectionGapBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ReflectionGapBoundaryUp.mk S H Sigma K P L Q T R N B =>
      [[BMark.b0],
        reflectionGapBoundaryEncodeBHist S,
        [BMark.b1, BMark.b0],
        reflectionGapBoundaryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b0],
        reflectionGapBoundaryEncodeBHist Sigma,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionGapBoundaryEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionGapBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionGapBoundaryEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionGapBoundaryEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        reflectionGapBoundaryEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        reflectionGapBoundaryEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        reflectionGapBoundaryEncodeBHist N,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionGapBoundaryEncodeBHist B]

def reflectionGapBoundaryFromEventFlow : EventFlow → Option ReflectionGapBoundaryUp
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
              | H :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Sigma :: rest5 =>
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
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | L :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | Q :: rest13 =>
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
                                                                      | R :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | B :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ReflectionGapBoundaryUp.mk
                                                                                                  (reflectionGapBoundaryDecodeBHist S)
                                                                                                  (reflectionGapBoundaryDecodeBHist H)
                                                                                                  (reflectionGapBoundaryDecodeBHist Sigma)
                                                                                                  (reflectionGapBoundaryDecodeBHist K)
                                                                                                  (reflectionGapBoundaryDecodeBHist P)
                                                                                                  (reflectionGapBoundaryDecodeBHist L)
                                                                                                  (reflectionGapBoundaryDecodeBHist Q)
                                                                                                  (reflectionGapBoundaryDecodeBHist T)
                                                                                                  (reflectionGapBoundaryDecodeBHist R)
                                                                                                  (reflectionGapBoundaryDecodeBHist N)
                                                                                                  (reflectionGapBoundaryDecodeBHist B))
                                                                                          | _ :: _ => none

private theorem reflectionGapBoundary_round_trip :
    ∀ x : ReflectionGapBoundaryUp,
      reflectionGapBoundaryFromEventFlow (reflectionGapBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S H Sigma K P L Q T R N B =>
      change
        some
          (ReflectionGapBoundaryUp.mk
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist S))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist H))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist Sigma))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist K))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist P))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist L))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist Q))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist T))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist R))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist N))
            (reflectionGapBoundaryDecodeBHist (reflectionGapBoundaryEncodeBHist B))) =
          some (ReflectionGapBoundaryUp.mk S H Sigma K P L Q T R N B)
      rw [reflectionGapBoundaryDecode_encode_bhist S,
        reflectionGapBoundaryDecode_encode_bhist H,
        reflectionGapBoundaryDecode_encode_bhist Sigma,
        reflectionGapBoundaryDecode_encode_bhist K,
        reflectionGapBoundaryDecode_encode_bhist P,
        reflectionGapBoundaryDecode_encode_bhist L,
        reflectionGapBoundaryDecode_encode_bhist Q,
        reflectionGapBoundaryDecode_encode_bhist T,
        reflectionGapBoundaryDecode_encode_bhist R,
        reflectionGapBoundaryDecode_encode_bhist N,
        reflectionGapBoundaryDecode_encode_bhist B]

private theorem reflectionGapBoundaryToEventFlow_injective {x y : ReflectionGapBoundaryUp} :
    reflectionGapBoundaryToEventFlow x = reflectionGapBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reflectionGapBoundaryFromEventFlow (reflectionGapBoundaryToEventFlow x) =
        reflectionGapBoundaryFromEventFlow (reflectionGapBoundaryToEventFlow y) :=
    congrArg reflectionGapBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (reflectionGapBoundary_round_trip x).symm
      (Eq.trans hread (reflectionGapBoundary_round_trip y)))

private theorem reflectionGapBoundary_field_faithful :
    ∀ x y : ReflectionGapBoundaryUp,
      reflectionGapBoundaryFields x = reflectionGapBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ H₁ Sigma₁ K₁ P₁ L₁ Q₁ T₁ R₁ N₁ B₁ =>
      cases y with
      | mk S₂ H₂ Sigma₂ K₂ P₂ L₂ Q₂ T₂ R₂ N₂ B₂ =>
          cases h
          rfl

instance reflectionGapBoundaryBHistCarrier : BHistCarrier ReflectionGapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reflectionGapBoundaryToEventFlow
  fromEventFlow := reflectionGapBoundaryFromEventFlow

instance reflectionGapBoundaryChapterTasteGate : ChapterTasteGate ReflectionGapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change reflectionGapBoundaryFromEventFlow (reflectionGapBoundaryToEventFlow x) = some x
    exact reflectionGapBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (reflectionGapBoundaryToEventFlow_injective heq)

instance reflectionGapBoundaryFieldFaithful : FieldFaithful ReflectionGapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := reflectionGapBoundaryFields
  field_faithful := reflectionGapBoundary_field_faithful

instance reflectionGapBoundaryNontrivial : Nontrivial ReflectionGapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ReflectionGapBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ReflectionGapBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ReflectionGapBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  reflectionGapBoundaryChapterTasteGate

theorem ReflectionGapBoundaryTasteGate_single_carrier_alignment :
    (∀ x : ReflectionGapBoundaryUp,
      reflectionGapBoundaryFromEventFlow (reflectionGapBoundaryToEventFlow x) = some x) ∧
      (∀ x y : ReflectionGapBoundaryUp,
        reflectionGapBoundaryToEventFlow x = reflectionGapBoundaryToEventFlow y → x = y) ∧
        (∀ (x : ReflectionGapBoundaryUp) w m,
          List.Mem w (reflectionGapBoundaryToEventFlow x) → List.Mem m w →
            m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact reflectionGapBoundary_round_trip
  · constructor
    · intro x y heq
      exact reflectionGapBoundaryToEventFlow_injective heq
    · intro _x _w _m hw hm
      exact event_flow_conservativity hw hm

end BEDC.Derived.ReflectionGapBoundaryUp.TasteGate
