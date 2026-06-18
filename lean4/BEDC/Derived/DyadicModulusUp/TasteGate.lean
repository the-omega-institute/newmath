import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicModulusUp : Type where
  | mk (D S R E H C P N : BHist) : DyadicModulusUp
  deriving DecidableEq

def dyadicModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicModulusEncodeBHist h

def dyadicModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicModulusDecodeBHist tail)

private theorem dyadicModulus_decode_encode_bhist :
    ∀ h : BHist, dyadicModulusDecodeBHist (dyadicModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicModulusFields : DyadicModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicModulusUp.mk D S R E H C P N => [D, S, R, E, H, C, P, N]

def dyadicModulusToEventFlow : DyadicModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map dyadicModulusEncodeBHist (dyadicModulusFields x)

def dyadicModulusFromEventFlow : EventFlow → Option DyadicModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (DyadicModulusUp.mk
                                          (dyadicModulusDecodeBHist D)
                                          (dyadicModulusDecodeBHist S)
                                          (dyadicModulusDecodeBHist R)
                                          (dyadicModulusDecodeBHist E)
                                          (dyadicModulusDecodeBHist H)
                                          (dyadicModulusDecodeBHist C)
                                          (dyadicModulusDecodeBHist P)
                                          (dyadicModulusDecodeBHist N))
                                  | _ :: _ => none

private theorem dyadicModulus_round_trip :
    ∀ x : DyadicModulusUp,
      dyadicModulusFromEventFlow (dyadicModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E H C P N =>
      change
        some
          (DyadicModulusUp.mk
            (dyadicModulusDecodeBHist (dyadicModulusEncodeBHist D))
            (dyadicModulusDecodeBHist (dyadicModulusEncodeBHist S))
            (dyadicModulusDecodeBHist (dyadicModulusEncodeBHist R))
            (dyadicModulusDecodeBHist (dyadicModulusEncodeBHist E))
            (dyadicModulusDecodeBHist (dyadicModulusEncodeBHist H))
            (dyadicModulusDecodeBHist (dyadicModulusEncodeBHist C))
            (dyadicModulusDecodeBHist (dyadicModulusEncodeBHist P))
            (dyadicModulusDecodeBHist (dyadicModulusEncodeBHist N))) =
          some (DyadicModulusUp.mk D S R E H C P N)
      rw [dyadicModulus_decode_encode_bhist D,
        dyadicModulus_decode_encode_bhist S,
        dyadicModulus_decode_encode_bhist R,
        dyadicModulus_decode_encode_bhist E,
        dyadicModulus_decode_encode_bhist H,
        dyadicModulus_decode_encode_bhist C,
        dyadicModulus_decode_encode_bhist P,
        dyadicModulus_decode_encode_bhist N]

private theorem dyadicModulusToEventFlow_injective
    {x y : DyadicModulusUp} :
    dyadicModulusToEventFlow x = dyadicModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicModulusFromEventFlow (dyadicModulusToEventFlow x) =
        dyadicModulusFromEventFlow (dyadicModulusToEventFlow y) :=
    congrArg dyadicModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicModulus_round_trip x).symm
      (Eq.trans hread (dyadicModulus_round_trip y)))

private theorem dyadicModulus_field_faithful :
    ∀ x y : DyadicModulusUp, dyadicModulusFields x = dyadicModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hD tail0
          injection tail0 with hS tail1
          injection tail1 with hR tail2
          injection tail2 with hE tail3
          injection tail3 with hH tail4
          injection tail4 with hC tail5
          injection tail5 with hP tail6
          injection tail6 with hN _
          subst hD
          subst hS
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance dyadicModulusBHistCarrier : BHistCarrier DyadicModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicModulusToEventFlow
  fromEventFlow := dyadicModulusFromEventFlow

instance dyadicModulusChapterTasteGate : ChapterTasteGate DyadicModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicModulusFromEventFlow (dyadicModulusToEventFlow x) = some x
    exact dyadicModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicModulusToEventFlow_injective heq)

instance dyadicModulusFieldFaithful : FieldFaithful DyadicModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicModulusFields
  field_faithful := dyadicModulus_field_faithful

instance dyadicModulusNontrivial : Nontrivial DyadicModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicModulusChapterTasteGate

def taste_gate_witness : ChapterTasteGate DyadicModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicModulusChapterTasteGate

theorem DyadicModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicModulusDecodeBHist (dyadicModulusEncodeBHist h) = h) ∧
      (∀ x : DyadicModulusUp,
        dyadicModulusFromEventFlow (dyadicModulusToEventFlow x) = some x) ∧
        dyadicModulusEncodeBHist BHist.Empty = ([] : List BMark) ∧
          Nonempty (ChapterTasteGate DyadicModulusUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicModulus_decode_encode_bhist
  · constructor
    · exact dyadicModulus_round_trip
    · constructor
      · rfl
      · exact ⟨dyadicModulusChapterTasteGate⟩

end BEDC.Derived.DyadicModulusUp
