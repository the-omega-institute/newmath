import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCriterionEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCriterionEquivalenceUp : Type where
  | mk (S Q M D R E H C P N : BHist) : CauchyCriterionEquivalenceUp
  deriving DecidableEq

def cauchyCriterionEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCriterionEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCriterionEquivalenceEncodeBHist h

def cauchyCriterionEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCriterionEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCriterionEquivalenceDecodeBHist tail)

private theorem CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCriterionEquivalenceDecodeBHist (cauchyCriterionEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCriterionEquivalenceFields : CauchyCriterionEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCriterionEquivalenceUp.mk S Q M D R E H C P N => [S, Q, M, D, R, E, H, C, P, N]

def cauchyCriterionEquivalenceToEventFlow : CauchyCriterionEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCriterionEquivalenceFields x).map cauchyCriterionEquivalenceEncodeBHist

def cauchyCriterionEquivalenceFromEventFlow : EventFlow → Option CauchyCriterionEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | M :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
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
                                                (CauchyCriterionEquivalenceUp.mk
                                                  (cauchyCriterionEquivalenceDecodeBHist S)
                                                  (cauchyCriterionEquivalenceDecodeBHist Q)
                                                  (cauchyCriterionEquivalenceDecodeBHist M)
                                                  (cauchyCriterionEquivalenceDecodeBHist D)
                                                  (cauchyCriterionEquivalenceDecodeBHist R)
                                                  (cauchyCriterionEquivalenceDecodeBHist E)
                                                  (cauchyCriterionEquivalenceDecodeBHist H)
                                                  (cauchyCriterionEquivalenceDecodeBHist C)
                                                  (cauchyCriterionEquivalenceDecodeBHist P)
                                                  (cauchyCriterionEquivalenceDecodeBHist N))
                                          | _ :: _ => none

private theorem CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCriterionEquivalenceUp,
      cauchyCriterionEquivalenceFromEventFlow (cauchyCriterionEquivalenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q M D R E H C P N =>
      change
        some
          (CauchyCriterionEquivalenceUp.mk
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist S))
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist Q))
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist M))
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist D))
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist R))
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist E))
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist H))
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist C))
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist P))
            (cauchyCriterionEquivalenceDecodeBHist
              (cauchyCriterionEquivalenceEncodeBHist N))) =
          some (CauchyCriterionEquivalenceUp.mk S Q M D R E H C P N)
      rw [CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode M,
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode D,
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCriterionEquivalenceUp} :
    cauchyCriterionEquivalenceToEventFlow x = cauchyCriterionEquivalenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCriterionEquivalenceFromEventFlow (cauchyCriterionEquivalenceToEventFlow x) =
        cauchyCriterionEquivalenceFromEventFlow (cauchyCriterionEquivalenceToEventFlow y) :=
    congrArg cauchyCriterionEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyCriterionEquivalenceUp,
      cauchyCriterionEquivalenceFields x = cauchyCriterionEquivalenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ Q₁ M₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Q₂ M₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS tail0
          injection tail0 with hQ tail1
          injection tail1 with hM tail2
          injection tail2 with hD tail3
          injection tail3 with hR tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hS
          subst hQ
          subst hM
          subst hD
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyCriterionEquivalenceBHistCarrier :
    BHistCarrier CauchyCriterionEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCriterionEquivalenceToEventFlow
  fromEventFlow := cauchyCriterionEquivalenceFromEventFlow

instance cauchyCriterionEquivalenceChapterTasteGate :
    ChapterTasteGate CauchyCriterionEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCriterionEquivalenceFromEventFlow (cauchyCriterionEquivalenceToEventFlow x) =
        some x
    exact CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyCriterionEquivalenceFieldFaithful :
    FieldFaithful CauchyCriterionEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCriterionEquivalenceFields
  field_faithful := CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_fields_faithful

instance cauchyCriterionEquivalenceNontrivial : Nontrivial CauchyCriterionEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCriterionEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCriterionEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyCriterionEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCriterionEquivalenceDecodeBHist (cauchyCriterionEquivalenceEncodeBHist h) = h) ∧
      (∀ x : CauchyCriterionEquivalenceUp,
        cauchyCriterionEquivalenceFromEventFlow
            (cauchyCriterionEquivalenceToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyCriterionEquivalenceUp,
          cauchyCriterionEquivalenceToEventFlow x =
              cauchyCriterionEquivalenceToEventFlow y →
            x = y) ∧
          cauchyCriterionEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : CauchyCriterionEquivalenceUp,
              cauchyCriterionEquivalenceFields x = cauchyCriterionEquivalenceFields y →
                x = y) ∧
              (∃ x y : CauchyCriterionEquivalenceUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_decode_encode,
      CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      CauchyCriterionEquivalenceTasteGate_single_carrier_alignment_fields_faithful,
      ⟨CauchyCriterionEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        CauchyCriterionEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.CauchyCriterionEquivalenceUp
