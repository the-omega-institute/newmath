import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicModulusChoiceFreeRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicModulusChoiceFreeRefinementUp : Type where
  | mk (D Q W S R E H C P N : BHist) : DyadicModulusChoiceFreeRefinementUp
  deriving DecidableEq

def dyadicModulusChoiceFreeRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicModulusChoiceFreeRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicModulusChoiceFreeRefinementEncodeBHist h

def dyadicModulusChoiceFreeRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicModulusChoiceFreeRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicModulusChoiceFreeRefinementDecodeBHist tail)

private theorem dyadicModulusChoiceFreeRefinement_decode_encode_bhist :
    ∀ h : BHist,
      dyadicModulusChoiceFreeRefinementDecodeBHist
          (dyadicModulusChoiceFreeRefinementEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicModulusChoiceFreeRefinementFields :
    DyadicModulusChoiceFreeRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicModulusChoiceFreeRefinementUp.mk D Q W S R E H C P N =>
      [D, Q, W, S, R, E, H, C, P, N]

def dyadicModulusChoiceFreeRefinementToEventFlow :
    DyadicModulusChoiceFreeRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map dyadicModulusChoiceFreeRefinementEncodeBHist
        (dyadicModulusChoiceFreeRefinementFields x)

def dyadicModulusChoiceFreeRefinementFromEventFlow :
    EventFlow → Option DyadicModulusChoiceFreeRefinementUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                                (DyadicModulusChoiceFreeRefinementUp.mk
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist D)
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist Q)
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist W)
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist S)
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist R)
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist E)
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist H)
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist C)
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist P)
                                                  (dyadicModulusChoiceFreeRefinementDecodeBHist N))
                                          | _ :: _ => none

private theorem dyadicModulusChoiceFreeRefinement_round_trip :
    ∀ x : DyadicModulusChoiceFreeRefinementUp,
      dyadicModulusChoiceFreeRefinementFromEventFlow
          (dyadicModulusChoiceFreeRefinementToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D Q W S R E H C P N =>
      change
        some
          (DyadicModulusChoiceFreeRefinementUp.mk
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist D))
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist Q))
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist W))
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist S))
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist R))
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist E))
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist H))
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist C))
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist P))
            (dyadicModulusChoiceFreeRefinementDecodeBHist
              (dyadicModulusChoiceFreeRefinementEncodeBHist N))) =
          some (DyadicModulusChoiceFreeRefinementUp.mk D Q W S R E H C P N)
      rw [dyadicModulusChoiceFreeRefinement_decode_encode_bhist D,
        dyadicModulusChoiceFreeRefinement_decode_encode_bhist Q,
        dyadicModulusChoiceFreeRefinement_decode_encode_bhist W,
        dyadicModulusChoiceFreeRefinement_decode_encode_bhist S,
        dyadicModulusChoiceFreeRefinement_decode_encode_bhist R,
        dyadicModulusChoiceFreeRefinement_decode_encode_bhist E,
        dyadicModulusChoiceFreeRefinement_decode_encode_bhist H,
        dyadicModulusChoiceFreeRefinement_decode_encode_bhist C,
        dyadicModulusChoiceFreeRefinement_decode_encode_bhist P,
        dyadicModulusChoiceFreeRefinement_decode_encode_bhist N]

private theorem dyadicModulusChoiceFreeRefinementToEventFlow_injective
    {x y : DyadicModulusChoiceFreeRefinementUp} :
    dyadicModulusChoiceFreeRefinementToEventFlow x =
        dyadicModulusChoiceFreeRefinementToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicModulusChoiceFreeRefinementFromEventFlow
          (dyadicModulusChoiceFreeRefinementToEventFlow x) =
        dyadicModulusChoiceFreeRefinementFromEventFlow
          (dyadicModulusChoiceFreeRefinementToEventFlow y) :=
    congrArg dyadicModulusChoiceFreeRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicModulusChoiceFreeRefinement_round_trip x).symm
      (Eq.trans hread (dyadicModulusChoiceFreeRefinement_round_trip y)))

private theorem dyadicModulusChoiceFreeRefinement_field_faithful :
    ∀ x y : DyadicModulusChoiceFreeRefinementUp,
      dyadicModulusChoiceFreeRefinementFields x =
          dyadicModulusChoiceFreeRefinementFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ Q₁ W₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ Q₂ W₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hD tail0
          injection tail0 with hQ tail1
          injection tail1 with hW tail2
          injection tail2 with hS tail3
          injection tail3 with hR tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hD
          subst hQ
          subst hW
          subst hS
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance dyadicModulusChoiceFreeRefinementBHistCarrier :
    BHistCarrier DyadicModulusChoiceFreeRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicModulusChoiceFreeRefinementToEventFlow
  fromEventFlow := dyadicModulusChoiceFreeRefinementFromEventFlow

instance dyadicModulusChoiceFreeRefinementChapterTasteGate :
    ChapterTasteGate DyadicModulusChoiceFreeRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicModulusChoiceFreeRefinementFromEventFlow
          (dyadicModulusChoiceFreeRefinementToEventFlow x) =
        some x
    exact dyadicModulusChoiceFreeRefinement_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicModulusChoiceFreeRefinementToEventFlow_injective heq)

instance dyadicModulusChoiceFreeRefinementFieldFaithful :
    FieldFaithful DyadicModulusChoiceFreeRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicModulusChoiceFreeRefinementFields
  field_faithful := dyadicModulusChoiceFreeRefinement_field_faithful

instance dyadicModulusChoiceFreeRefinementNontrivial :
    Nontrivial DyadicModulusChoiceFreeRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicModulusChoiceFreeRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DyadicModulusChoiceFreeRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicModulusChoiceFreeRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicModulusChoiceFreeRefinementChapterTasteGate

def taste_gate_witness : ChapterTasteGate DyadicModulusChoiceFreeRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicModulusChoiceFreeRefinementChapterTasteGate

theorem DyadicModulusChoiceFreeRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicModulusChoiceFreeRefinementDecodeBHist
          (dyadicModulusChoiceFreeRefinementEncodeBHist h) =
        h) ∧
      (∀ x : DyadicModulusChoiceFreeRefinementUp,
        dyadicModulusChoiceFreeRefinementFromEventFlow
            (dyadicModulusChoiceFreeRefinementToEventFlow x) =
          some x) ∧
        dyadicModulusChoiceFreeRefinementEncodeBHist BHist.Empty = ([] : List BMark) ∧
          Nonempty (ChapterTasteGate DyadicModulusChoiceFreeRefinementUp) ∧
            Nonempty (FieldFaithful DyadicModulusChoiceFreeRefinementUp) ∧
              Nonempty (Nontrivial DyadicModulusChoiceFreeRefinementUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact dyadicModulusChoiceFreeRefinement_decode_encode_bhist
  · constructor
    · exact dyadicModulusChoiceFreeRefinement_round_trip
    · constructor
      · rfl
      · constructor
        · exact ⟨dyadicModulusChoiceFreeRefinementChapterTasteGate⟩
        · constructor
          · exact ⟨dyadicModulusChoiceFreeRefinementFieldFaithful⟩
          · exact ⟨dyadicModulusChoiceFreeRefinementNontrivial⟩

end BEDC.Derived.DyadicModulusChoiceFreeRefinementUp
