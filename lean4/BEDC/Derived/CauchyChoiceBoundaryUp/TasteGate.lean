import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyChoiceBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyChoiceBoundaryUp : Type where
  | mk (M E I T S R H C P N : BHist) : CauchyChoiceBoundaryUp
  deriving DecidableEq

def cauchyChoiceBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyChoiceBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyChoiceBoundaryEncodeBHist h

def cauchyChoiceBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyChoiceBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyChoiceBoundaryDecodeBHist tail)

private theorem cauchyChoiceBoundary_decode_encode_bhist :
    ∀ h : BHist, cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyChoiceBoundaryFields : CauchyChoiceBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyChoiceBoundaryUp.mk M E I T S R H C P N => [M, E, I, T, S, R, H, C, P, N]

def cauchyChoiceBoundaryToEventFlow : CauchyChoiceBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyChoiceBoundaryUp.mk M E I T S R H C P N =>
      [cauchyChoiceBoundaryEncodeBHist M,
        cauchyChoiceBoundaryEncodeBHist E,
        cauchyChoiceBoundaryEncodeBHist I,
        cauchyChoiceBoundaryEncodeBHist T,
        cauchyChoiceBoundaryEncodeBHist S,
        cauchyChoiceBoundaryEncodeBHist R,
        cauchyChoiceBoundaryEncodeBHist H,
        cauchyChoiceBoundaryEncodeBHist C,
        cauchyChoiceBoundaryEncodeBHist P,
        cauchyChoiceBoundaryEncodeBHist N]

def cauchyChoiceBoundaryFromEventFlow :
    EventFlow → Option CauchyChoiceBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | I :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyChoiceBoundaryUp.mk
                                                  (cauchyChoiceBoundaryDecodeBHist M)
                                                  (cauchyChoiceBoundaryDecodeBHist E)
                                                  (cauchyChoiceBoundaryDecodeBHist I)
                                                  (cauchyChoiceBoundaryDecodeBHist T)
                                                  (cauchyChoiceBoundaryDecodeBHist S)
                                                  (cauchyChoiceBoundaryDecodeBHist R)
                                                  (cauchyChoiceBoundaryDecodeBHist H)
                                                  (cauchyChoiceBoundaryDecodeBHist C)
                                                  (cauchyChoiceBoundaryDecodeBHist P)
                                                  (cauchyChoiceBoundaryDecodeBHist N))
                                          | _ :: _ => none

private theorem cauchyChoiceBoundary_round_trip :
    ∀ x : CauchyChoiceBoundaryUp,
      cauchyChoiceBoundaryFromEventFlow (cauchyChoiceBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E I T S R H C P N =>
      change
        some
          (CauchyChoiceBoundaryUp.mk
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist M))
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist E))
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist I))
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist T))
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist S))
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist R))
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist H))
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist C))
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist P))
            (cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist N))) =
          some (CauchyChoiceBoundaryUp.mk M E I T S R H C P N)
      rw [cauchyChoiceBoundary_decode_encode_bhist M,
        cauchyChoiceBoundary_decode_encode_bhist E,
        cauchyChoiceBoundary_decode_encode_bhist I,
        cauchyChoiceBoundary_decode_encode_bhist T,
        cauchyChoiceBoundary_decode_encode_bhist S,
        cauchyChoiceBoundary_decode_encode_bhist R,
        cauchyChoiceBoundary_decode_encode_bhist H,
        cauchyChoiceBoundary_decode_encode_bhist C,
        cauchyChoiceBoundary_decode_encode_bhist P,
        cauchyChoiceBoundary_decode_encode_bhist N]

private theorem cauchyChoiceBoundaryToEventFlow_injective
    {x y : CauchyChoiceBoundaryUp} :
    cauchyChoiceBoundaryToEventFlow x = cauchyChoiceBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyChoiceBoundaryFromEventFlow (cauchyChoiceBoundaryToEventFlow x) =
        cauchyChoiceBoundaryFromEventFlow (cauchyChoiceBoundaryToEventFlow y) :=
    congrArg cauchyChoiceBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyChoiceBoundary_round_trip x).symm
      (Eq.trans hread (cauchyChoiceBoundary_round_trip y)))

private theorem cauchyChoiceBoundary_field_faithful :
    ∀ x y : CauchyChoiceBoundaryUp,
      cauchyChoiceBoundaryFields x = cauchyChoiceBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk M₁ E₁ I₁ T₁ S₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ E₂ I₂ T₂ S₂ R₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance cauchyChoiceBoundaryBHistCarrier : BHistCarrier CauchyChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyChoiceBoundaryToEventFlow
  fromEventFlow := cauchyChoiceBoundaryFromEventFlow

instance cauchyChoiceBoundaryChapterTasteGate :
    ChapterTasteGate CauchyChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyChoiceBoundaryFromEventFlow (cauchyChoiceBoundaryToEventFlow x) = some x
    exact cauchyChoiceBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyChoiceBoundaryToEventFlow_injective heq)

instance cauchyChoiceBoundaryFieldFaithful : FieldFaithful CauchyChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyChoiceBoundaryFields
  field_faithful := cauchyChoiceBoundary_field_faithful

instance cauchyChoiceBoundaryNontrivial : Nontrivial CauchyChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyChoiceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyChoiceBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyChoiceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyChoiceBoundaryChapterTasteGate

theorem CauchyChoiceBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyChoiceBoundaryDecodeBHist (cauchyChoiceBoundaryEncodeBHist h) = h) ∧
      (∀ x : CauchyChoiceBoundaryUp,
        cauchyChoiceBoundaryFromEventFlow (cauchyChoiceBoundaryToEventFlow x) = some x) ∧
      (∀ x y : CauchyChoiceBoundaryUp,
        cauchyChoiceBoundaryToEventFlow x = cauchyChoiceBoundaryToEventFlow y → x = y) ∧
      Nonempty
        (@ChapterTasteGate CauchyChoiceBoundaryUp cauchyChoiceBoundaryBHistCarrier) ∧
      (∀ x y : CauchyChoiceBoundaryUp,
        cauchyChoiceBoundaryFields x = cauchyChoiceBoundaryFields y → x = y) ∧
      cauchyChoiceBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨cauchyChoiceBoundary_decode_encode_bhist, cauchyChoiceBoundary_round_trip,
    fun _ _ heq => cauchyChoiceBoundaryToEventFlow_injective heq,
    ⟨cauchyChoiceBoundaryChapterTasteGate⟩, cauchyChoiceBoundary_field_faithful, rfl⟩

end BEDC.Derived.CauchyChoiceBoundaryUp
