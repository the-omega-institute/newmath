import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HahnMazurkiewiczBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HahnMazurkiewiczBoundaryUp : Type where
  | mk :
      (K M C P B E T R N : BHist) →
      HahnMazurkiewiczBoundaryUp
  deriving DecidableEq

def hahnMazurkiewiczBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hahnMazurkiewiczBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hahnMazurkiewiczBoundaryEncodeBHist h

def hahnMazurkiewiczBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hahnMazurkiewiczBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hahnMazurkiewiczBoundaryDecodeBHist tail)

private theorem hahnMazurkiewiczBoundaryDecode_encode_bhist :
    ∀ h : BHist, hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hahnMazurkiewiczBoundaryToEventFlow : HahnMazurkiewiczBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HahnMazurkiewiczBoundaryUp.mk K M C P B E T R N =>
      [[BMark.b0],
        hahnMazurkiewiczBoundaryEncodeBHist K,
        [BMark.b1, BMark.b0],
        hahnMazurkiewiczBoundaryEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        hahnMazurkiewiczBoundaryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hahnMazurkiewiczBoundaryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hahnMazurkiewiczBoundaryEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hahnMazurkiewiczBoundaryEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hahnMazurkiewiczBoundaryEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hahnMazurkiewiczBoundaryEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hahnMazurkiewiczBoundaryEncodeBHist N]

def hahnMazurkiewiczBoundaryFromEventFlow : EventFlow → Option HahnMazurkiewiczBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | K :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | B :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | E :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | T :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | R :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (HahnMazurkiewiczBoundaryUp.mk
                                                                                  (hahnMazurkiewiczBoundaryDecodeBHist
                                                                                    K)
                                                                                  (hahnMazurkiewiczBoundaryDecodeBHist
                                                                                    M)
                                                                                  (hahnMazurkiewiczBoundaryDecodeBHist
                                                                                    C)
                                                                                  (hahnMazurkiewiczBoundaryDecodeBHist
                                                                                    P)
                                                                                  (hahnMazurkiewiczBoundaryDecodeBHist
                                                                                    B)
                                                                                  (hahnMazurkiewiczBoundaryDecodeBHist
                                                                                    E)
                                                                                  (hahnMazurkiewiczBoundaryDecodeBHist
                                                                                    T)
                                                                                  (hahnMazurkiewiczBoundaryDecodeBHist
                                                                                    R)
                                                                                  (hahnMazurkiewiczBoundaryDecodeBHist
                                                                                    N))
                                                                          | _ :: _ => none

private theorem hahnMazurkiewiczBoundary_round_trip :
    ∀ x : HahnMazurkiewiczBoundaryUp,
      hahnMazurkiewiczBoundaryFromEventFlow (hahnMazurkiewiczBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K M C P B E T R N =>
      change some
          (HahnMazurkiewiczBoundaryUp.mk
            (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist K))
            (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist M))
            (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist C))
            (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist P))
            (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist B))
            (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist E))
            (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist T))
            (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist R))
            (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist N))) =
          some (HahnMazurkiewiczBoundaryUp.mk K M C P B E T R N)
      rw [hahnMazurkiewiczBoundaryDecode_encode_bhist K,
        hahnMazurkiewiczBoundaryDecode_encode_bhist M,
        hahnMazurkiewiczBoundaryDecode_encode_bhist C,
        hahnMazurkiewiczBoundaryDecode_encode_bhist P,
        hahnMazurkiewiczBoundaryDecode_encode_bhist B,
        hahnMazurkiewiczBoundaryDecode_encode_bhist E,
        hahnMazurkiewiczBoundaryDecode_encode_bhist T,
        hahnMazurkiewiczBoundaryDecode_encode_bhist R,
        hahnMazurkiewiczBoundaryDecode_encode_bhist N]

private theorem hahnMazurkiewiczBoundaryToEventFlow_injective {x y : HahnMazurkiewiczBoundaryUp} :
    hahnMazurkiewiczBoundaryToEventFlow x = hahnMazurkiewiczBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hahnMazurkiewiczBoundaryFromEventFlow (hahnMazurkiewiczBoundaryToEventFlow x) =
        hahnMazurkiewiczBoundaryFromEventFlow (hahnMazurkiewiczBoundaryToEventFlow y) :=
    congrArg hahnMazurkiewiczBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hahnMazurkiewiczBoundary_round_trip x).symm
      (Eq.trans hread (hahnMazurkiewiczBoundary_round_trip y)))

instance hahnMazurkiewiczBoundaryBHistCarrier : BHistCarrier HahnMazurkiewiczBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hahnMazurkiewiczBoundaryToEventFlow
  fromEventFlow := hahnMazurkiewiczBoundaryFromEventFlow

instance hahnMazurkiewiczBoundaryChapterTasteGate :
    ChapterTasteGate HahnMazurkiewiczBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hahnMazurkiewiczBoundaryFromEventFlow (hahnMazurkiewiczBoundaryToEventFlow x) = some x
    exact hahnMazurkiewiczBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hahnMazurkiewiczBoundaryToEventFlow_injective heq)

def hahnMazurkiewiczBoundaryFields : HahnMazurkiewiczBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HahnMazurkiewiczBoundaryUp.mk K M C P B E T R N => [K, M, C, P, B, E, T, R, N]

theorem hahnMazurkiewiczBoundaryFields_faithful :
    ∀ x y : HahnMazurkiewiczBoundaryUp, hahnMazurkiewiczBoundaryFields x = hahnMazurkiewiczBoundaryFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  intro x y h
  cases x with
  | mk K₁ M₁ C₁ P₁ B₁ E₁ T₁ R₁ N₁ =>
      cases y with
      | mk K₂ M₂ C₂ P₂ B₂ E₂ T₂ R₂ N₂ =>
          injection h with hK tail0
          injection tail0 with hM tail1
          injection tail1 with hC tail2
          injection tail2 with hP tail3
          injection tail3 with hB tail4
          injection tail4 with hE tail5
          injection tail5 with hT tail6
          injection tail6 with hR tail7
          injection tail7 with hN _nil
          subst hK
          subst hM
          subst hC
          subst hP
          subst hB
          subst hE
          subst hT
          subst hR
          subst hN
          rfl

instance hahnMazurkiewiczBoundaryFieldFaithful : FieldFaithful HahnMazurkiewiczBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hahnMazurkiewiczBoundaryFields
  field_faithful := hahnMazurkiewiczBoundaryFields_faithful

instance hahnMazurkiewiczBoundaryNontrivial : Nontrivial HahnMazurkiewiczBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HahnMazurkiewiczBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HahnMazurkiewiczBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEncodeBHist h) = h) ∧
      (∀ x : HahnMazurkiewiczBoundaryUp,
        hahnMazurkiewiczBoundaryFromEventFlow (hahnMazurkiewiczBoundaryToEventFlow x) = some x) ∧
        (∀ x y : HahnMazurkiewiczBoundaryUp,
          hahnMazurkiewiczBoundaryToEventFlow x = hahnMazurkiewiczBoundaryToEventFlow y → x = y) ∧
          hahnMazurkiewiczBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact hahnMazurkiewiczBoundaryDecode_encode_bhist
  · constructor
    · exact hahnMazurkiewiczBoundary_round_trip
    · constructor
      · intro x y heq
        exact hahnMazurkiewiczBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.HahnMazurkiewiczBoundaryUp
