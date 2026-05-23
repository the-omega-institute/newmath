import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySubsequenceExtractionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySubsequenceExtractionUp : Type where
  | mk (S M D I W R H C P N : BHist) : CauchySubsequenceExtractionUp
  deriving DecidableEq

def cauchySubsequenceExtractionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySubsequenceExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySubsequenceExtractionEncodeBHist h

def cauchySubsequenceExtractionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySubsequenceExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySubsequenceExtractionDecodeBHist tail)

private theorem cauchySubsequenceExtractionDecode_encode :
    ∀ h : BHist,
      cauchySubsequenceExtractionDecodeBHist
        (cauchySubsequenceExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySubsequenceExtractionFields : CauchySubsequenceExtractionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySubsequenceExtractionUp.mk S M D I W R H C P N => [S, M, D, I, W, R, H, C, P, N]

def cauchySubsequenceExtractionToEventFlow : CauchySubsequenceExtractionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySubsequenceExtractionFields x).map cauchySubsequenceExtractionEncodeBHist

def cauchySubsequenceExtractionFromEventFlow : EventFlow -> Option CauchySubsequenceExtractionUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | M :: restM =>
          match restM with
          | D :: restD =>
              match restD with
              | I :: restI =>
                  match restI with
                  | W :: restW =>
                      match restW with
                      | R :: restR =>
                          match restR with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (CauchySubsequenceExtractionUp.mk
                                                  (cauchySubsequenceExtractionDecodeBHist S)
                                                  (cauchySubsequenceExtractionDecodeBHist M)
                                                  (cauchySubsequenceExtractionDecodeBHist D)
                                                  (cauchySubsequenceExtractionDecodeBHist I)
                                                  (cauchySubsequenceExtractionDecodeBHist W)
                                                  (cauchySubsequenceExtractionDecodeBHist R)
                                                  (cauchySubsequenceExtractionDecodeBHist H)
                                                  (cauchySubsequenceExtractionDecodeBHist C)
                                                  (cauchySubsequenceExtractionDecodeBHist P)
                                                  (cauchySubsequenceExtractionDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem cauchySubsequenceExtraction_round_trip :
    ∀ x : CauchySubsequenceExtractionUp,
      cauchySubsequenceExtractionFromEventFlow
        (cauchySubsequenceExtractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D I W R H C P N =>
      change
        some
          (CauchySubsequenceExtractionUp.mk
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist S))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist M))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist D))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist I))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist W))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist R))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist H))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist C))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist P))
            (cauchySubsequenceExtractionDecodeBHist
              (cauchySubsequenceExtractionEncodeBHist N))) =
          some (CauchySubsequenceExtractionUp.mk S M D I W R H C P N)
      rw [cauchySubsequenceExtractionDecode_encode S,
        cauchySubsequenceExtractionDecode_encode M,
        cauchySubsequenceExtractionDecode_encode D,
        cauchySubsequenceExtractionDecode_encode I,
        cauchySubsequenceExtractionDecode_encode W,
        cauchySubsequenceExtractionDecode_encode R,
        cauchySubsequenceExtractionDecode_encode H,
        cauchySubsequenceExtractionDecode_encode C,
        cauchySubsequenceExtractionDecode_encode P,
        cauchySubsequenceExtractionDecode_encode N]

private theorem cauchySubsequenceExtractionToEventFlow_injective
    {x y : CauchySubsequenceExtractionUp} :
    cauchySubsequenceExtractionToEventFlow x =
      cauchySubsequenceExtractionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySubsequenceExtractionFromEventFlow (cauchySubsequenceExtractionToEventFlow x) =
        cauchySubsequenceExtractionFromEventFlow (cauchySubsequenceExtractionToEventFlow y) :=
    congrArg cauchySubsequenceExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySubsequenceExtraction_round_trip x).symm
      (Eq.trans hread (cauchySubsequenceExtraction_round_trip y)))

private theorem cauchySubsequenceExtraction_field_faithful :
    ∀ x y : CauchySubsequenceExtractionUp,
      cauchySubsequenceExtractionFields x = cauchySubsequenceExtractionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S M D I W R H C P N =>
      cases y with
      | mk S' M' D' I' W' R' H' C' P' N' =>
          cases hfields
          rfl

instance cauchySubsequenceExtractionBHistCarrier :
    BHistCarrier CauchySubsequenceExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySubsequenceExtractionToEventFlow
  fromEventFlow := cauchySubsequenceExtractionFromEventFlow

instance cauchySubsequenceExtractionChapterTasteGate :
    ChapterTasteGate CauchySubsequenceExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySubsequenceExtractionFromEventFlow
      (cauchySubsequenceExtractionToEventFlow x) = some x
    exact cauchySubsequenceExtraction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySubsequenceExtractionToEventFlow_injective heq)

instance cauchySubsequenceExtractionFieldFaithful :
    FieldFaithful CauchySubsequenceExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySubsequenceExtractionFields
  field_faithful := cauchySubsequenceExtraction_field_faithful

instance cauchySubsequenceExtractionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchySubsequenceExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySubsequenceExtractionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySubsequenceExtractionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchySubsequenceExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySubsequenceExtractionChapterTasteGate

theorem CauchySubsequenceExtractionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchySubsequenceExtractionUp) ∧
      Nonempty (FieldFaithful CauchySubsequenceExtractionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchySubsequenceExtractionUp) ∧
      (∀ h : BHist,
        cauchySubsequenceExtractionDecodeBHist
          (cauchySubsequenceExtractionEncodeBHist h) = h) ∧
      (∀ x : CauchySubsequenceExtractionUp,
        cauchySubsequenceExtractionFromEventFlow
          (cauchySubsequenceExtractionToEventFlow x) = some x) ∧
      (∀ x y : CauchySubsequenceExtractionUp,
        cauchySubsequenceExtractionToEventFlow x =
          cauchySubsequenceExtractionToEventFlow y -> x = y) ∧
      cauchySubsequenceExtractionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchySubsequenceExtractionChapterTasteGate⟩,
      ⟨cauchySubsequenceExtractionFieldFaithful⟩,
      ⟨cauchySubsequenceExtractionNontrivial⟩,
      cauchySubsequenceExtractionDecode_encode,
      cauchySubsequenceExtraction_round_trip,
      by
        intro x y heq
        exact cauchySubsequenceExtractionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchySubsequenceExtractionUp.TasteGate
