import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CandidateSetNormalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CandidateSetNormalizationUp : Type where
  | mk (K T A I O H C P N : BHist) : CandidateSetNormalizationUp
  deriving DecidableEq

def candidateSetNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: candidateSetNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: candidateSetNormalizationEncodeBHist h

def candidateSetNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (candidateSetNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (candidateSetNormalizationDecodeBHist tail)

private theorem candidateSetNormalizationDecode_encode_bhist :
    ∀ h : BHist,
      candidateSetNormalizationDecodeBHist (candidateSetNormalizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def candidateSetNormalizationFields : CandidateSetNormalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CandidateSetNormalizationUp.mk K T A I O H C P N => [K, T, A, I, O, H, C, P, N]

def candidateSetNormalizationToEventFlow : CandidateSetNormalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map candidateSetNormalizationEncodeBHist (candidateSetNormalizationFields x)

def candidateSetNormalizationFromEventFlow : EventFlow → Option CandidateSetNormalizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: restK =>
      match restK with
      | [] => none
      | T :: restT =>
          match restT with
          | [] => none
          | A :: restA =>
              match restA with
              | [] => none
              | I :: restI =>
                  match restI with
                  | [] => none
                  | O :: restO =>
                      match restO with
                      | [] => none
                      | H :: restH =>
                          match restH with
                          | [] => none
                          | C :: restC =>
                              match restC with
                              | [] => none
                              | P :: restP =>
                                  match restP with
                                  | [] => none
                                  | N :: restN =>
                                      match restN with
                                      | [] =>
                                          some
                                            (CandidateSetNormalizationUp.mk
                                              (candidateSetNormalizationDecodeBHist K)
                                              (candidateSetNormalizationDecodeBHist T)
                                              (candidateSetNormalizationDecodeBHist A)
                                              (candidateSetNormalizationDecodeBHist I)
                                              (candidateSetNormalizationDecodeBHist O)
                                              (candidateSetNormalizationDecodeBHist H)
                                              (candidateSetNormalizationDecodeBHist C)
                                              (candidateSetNormalizationDecodeBHist P)
                                              (candidateSetNormalizationDecodeBHist N))
                                      | _ :: _ => none

private theorem candidateSetNormalization_round_trip :
    ∀ x : CandidateSetNormalizationUp,
      candidateSetNormalizationFromEventFlow (candidateSetNormalizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K T A I O H C P N =>
      change
        some
          (CandidateSetNormalizationUp.mk
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist K))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist T))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist A))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist I))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist O))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist H))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist C))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist P))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist N))) =
          some (CandidateSetNormalizationUp.mk K T A I O H C P N)
      rw [candidateSetNormalizationDecode_encode_bhist K,
        candidateSetNormalizationDecode_encode_bhist T,
        candidateSetNormalizationDecode_encode_bhist A,
        candidateSetNormalizationDecode_encode_bhist I,
        candidateSetNormalizationDecode_encode_bhist O,
        candidateSetNormalizationDecode_encode_bhist H,
        candidateSetNormalizationDecode_encode_bhist C,
        candidateSetNormalizationDecode_encode_bhist P,
        candidateSetNormalizationDecode_encode_bhist N]

private theorem candidateSetNormalizationToEventFlow_injective
    {x y : CandidateSetNormalizationUp} :
    candidateSetNormalizationToEventFlow x = candidateSetNormalizationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      candidateSetNormalizationFromEventFlow (candidateSetNormalizationToEventFlow x) =
        candidateSetNormalizationFromEventFlow (candidateSetNormalizationToEventFlow y) :=
    congrArg candidateSetNormalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (candidateSetNormalization_round_trip x).symm
      (Eq.trans hread (candidateSetNormalization_round_trip y)))

private theorem candidateSetNormalization_fields_faithful :
    ∀ x y : CandidateSetNormalizationUp,
      candidateSetNormalizationFields x = candidateSetNormalizationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk K₁ T₁ A₁ I₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ T₂ A₂ I₂ O₂ H₂ C₂ P₂ N₂ =>
          injection h with hK tail0
          injection tail0 with hT tail1
          injection tail1 with hA tail2
          injection tail2 with hI tail3
          injection tail3 with hO tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hK
          subst hT
          subst hA
          subst hI
          subst hO
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance candidateSetNormalizationBHistCarrier : BHistCarrier CandidateSetNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := candidateSetNormalizationToEventFlow
  fromEventFlow := candidateSetNormalizationFromEventFlow

instance candidateSetNormalizationChapterTasteGate :
    ChapterTasteGate CandidateSetNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      candidateSetNormalizationFromEventFlow (candidateSetNormalizationToEventFlow x) =
        some x
    exact candidateSetNormalization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (candidateSetNormalizationToEventFlow_injective heq)

instance candidateSetNormalizationFieldFaithful : FieldFaithful CandidateSetNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := candidateSetNormalizationFields
  field_faithful := candidateSetNormalization_fields_faithful

instance candidateSetNormalizationNontrivial : Nontrivial CandidateSetNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CandidateSetNormalizationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CandidateSetNormalizationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CandidateSetNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  candidateSetNormalizationChapterTasteGate

theorem CandidateSetNormalizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      candidateSetNormalizationDecodeBHist (candidateSetNormalizationEncodeBHist h) = h) ∧
      (∀ x : CandidateSetNormalizationUp,
        candidateSetNormalizationFromEventFlow (candidateSetNormalizationToEventFlow x) =
          some x) ∧
        (∀ x y : CandidateSetNormalizationUp,
          candidateSetNormalizationToEventFlow x =
              candidateSetNormalizationToEventFlow y →
            x = y) ∧
          candidateSetNormalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact candidateSetNormalizationDecode_encode_bhist
  · constructor
    · exact candidateSetNormalization_round_trip
    · constructor
      · intro x y heq
        exact candidateSetNormalizationToEventFlow_injective heq
      · rfl

theorem CandidateSetNormalizationTasteGate_fieldfaithful_nontrivial :
    Nonempty (BHistCarrier CandidateSetNormalizationUp) ∧
      Nonempty (ChapterTasteGate CandidateSetNormalizationUp) ∧
        Nonempty (FieldFaithful CandidateSetNormalizationUp) ∧
          Nonempty (Nontrivial CandidateSetNormalizationUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨candidateSetNormalizationBHistCarrier⟩,
      ⟨candidateSetNormalizationChapterTasteGate⟩,
      ⟨candidateSetNormalizationFieldFaithful⟩,
      ⟨candidateSetNormalizationNontrivial⟩⟩

end BEDC.Derived.CandidateSetNormalizationUp
