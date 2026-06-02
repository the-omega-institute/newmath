import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RaikovCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RaikovCompletionUp : Type where
  | mk : (G U S L R F C H P N : BHist) → RaikovCompletionUp
  deriving DecidableEq

def raikovCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: raikovCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: raikovCompletionEncodeBHist h

def raikovCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (raikovCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (raikovCompletionDecodeBHist tail)

private theorem RaikovCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, raikovCompletionDecodeBHist (raikovCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def raikovCompletionFields : RaikovCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RaikovCompletionUp.mk G U S L R F C H P N => [G, U, S, L, R, F, C, H, P, N]

def raikovCompletionToEventFlow : RaikovCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (raikovCompletionFields x).map raikovCompletionEncodeBHist

def raikovCompletionFromEventFlow : EventFlow → Option RaikovCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | G :: rest0 =>
      match rest0 with
      | [] => none
      | U :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (RaikovCompletionUp.mk
                                                  (raikovCompletionDecodeBHist G)
                                                  (raikovCompletionDecodeBHist U)
                                                  (raikovCompletionDecodeBHist S)
                                                  (raikovCompletionDecodeBHist L)
                                                  (raikovCompletionDecodeBHist R)
                                                  (raikovCompletionDecodeBHist F)
                                                  (raikovCompletionDecodeBHist C)
                                                  (raikovCompletionDecodeBHist H)
                                                  (raikovCompletionDecodeBHist P)
                                                  (raikovCompletionDecodeBHist N))
                                          | _ :: _ => none

private theorem RaikovCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RaikovCompletionUp,
      raikovCompletionFromEventFlow (raikovCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G U S L R F C H P N =>
      change
        some
          (RaikovCompletionUp.mk
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist G))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist U))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist S))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist L))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist R))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist F))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist C))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist H))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist P))
            (raikovCompletionDecodeBHist (raikovCompletionEncodeBHist N))) =
          some (RaikovCompletionUp.mk G U S L R F C H P N)
      rw [RaikovCompletionTasteGate_single_carrier_alignment_decode_encode G,
        RaikovCompletionTasteGate_single_carrier_alignment_decode_encode U,
        RaikovCompletionTasteGate_single_carrier_alignment_decode_encode S,
        RaikovCompletionTasteGate_single_carrier_alignment_decode_encode L,
        RaikovCompletionTasteGate_single_carrier_alignment_decode_encode R,
        RaikovCompletionTasteGate_single_carrier_alignment_decode_encode F,
        RaikovCompletionTasteGate_single_carrier_alignment_decode_encode C,
        RaikovCompletionTasteGate_single_carrier_alignment_decode_encode H,
        RaikovCompletionTasteGate_single_carrier_alignment_decode_encode P,
        RaikovCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem RaikovCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RaikovCompletionUp} :
    raikovCompletionToEventFlow x = raikovCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      raikovCompletionFromEventFlow (raikovCompletionToEventFlow x) =
        raikovCompletionFromEventFlow (raikovCompletionToEventFlow y) :=
    congrArg raikovCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RaikovCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RaikovCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem RaikovCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RaikovCompletionUp,
      raikovCompletionFields x = raikovCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ U₁ S₁ L₁ R₁ F₁ C₁ H₁ P₁ N₁ =>
      cases y with
      | mk G₂ U₂ S₂ L₂ R₂ F₂ C₂ H₂ P₂ N₂ =>
          injection hfields with hG tail0
          injection tail0 with hU tail1
          injection tail1 with hS tail2
          injection tail2 with hL tail3
          injection tail3 with hR tail4
          injection tail4 with hF tail5
          injection tail5 with hC tail6
          injection tail6 with hH tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hG
          subst hU
          subst hS
          subst hL
          subst hR
          subst hF
          subst hC
          subst hH
          subst hP
          subst hN
          rfl

instance raikovCompletionBHistCarrier : BHistCarrier RaikovCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := raikovCompletionToEventFlow
  fromEventFlow := raikovCompletionFromEventFlow

instance raikovCompletionChapterTasteGate : ChapterTasteGate RaikovCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change raikovCompletionFromEventFlow (raikovCompletionToEventFlow x) = some x
    exact RaikovCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RaikovCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance raikovCompletionFieldFaithful : FieldFaithful RaikovCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := raikovCompletionFields
  field_faithful := RaikovCompletionTasteGate_single_carrier_alignment_fields_faithful

instance raikovCompletionNontrivial : BEDC.Meta.TasteGate.Nontrivial RaikovCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RaikovCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RaikovCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RaikovCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  raikovCompletionChapterTasteGate

theorem RaikovCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RaikovCompletionUp) ∧
      Nonempty (FieldFaithful RaikovCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RaikovCompletionUp) ∧
          (∀ h : BHist, raikovCompletionDecodeBHist (raikovCompletionEncodeBHist h) = h) ∧
            (∀ x : RaikovCompletionUp,
              raikovCompletionFromEventFlow (raikovCompletionToEventFlow x) = some x) ∧
              (∀ x y : RaikovCompletionUp,
                raikovCompletionToEventFlow x = raikovCompletionToEventFlow y → x = y) ∧
                raikovCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨raikovCompletionChapterTasteGate⟩, ⟨raikovCompletionFieldFaithful⟩,
      ⟨raikovCompletionNontrivial⟩,
      RaikovCompletionTasteGate_single_carrier_alignment_decode_encode,
      RaikovCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RaikovCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RaikovCompletionUp
