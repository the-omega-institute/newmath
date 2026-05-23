import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySubsequenceExtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySubsequenceExtractionUp : Type where
  | mk (S M D I W R H C P N : BHist) : CauchySubsequenceExtractionUp
  deriving DecidableEq

def cauchySubsequenceExtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySubsequenceExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySubsequenceExtractionEncodeBHist h

def cauchySubsequenceExtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySubsequenceExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySubsequenceExtractionDecodeBHist tail)

private theorem CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchySubsequenceExtractionDecodeBHist
        (cauchySubsequenceExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySubsequenceExtractionFields : CauchySubsequenceExtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySubsequenceExtractionUp.mk S M D I W R H C P N => [S, M, D, I, W, R, H, C, P, N]

def cauchySubsequenceExtractionToEventFlow : CauchySubsequenceExtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySubsequenceExtractionFields x).map cauchySubsequenceExtractionEncodeBHist

def cauchySubsequenceExtractionFromEventFlow :
    EventFlow → Option CauchySubsequenceExtractionUp
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

private theorem cauchySubsequenceExtraction_mk_congr
    {S S' M M' D D' I I' W W' R R' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hM : M' = M) (hD : D' = D) (hI : I' = I)
    (hW : W' = W) (hR : R' = R) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchySubsequenceExtractionUp.mk S' M' D' I' W' R' H' C' P' N' =
      CauchySubsequenceExtractionUp.mk S M D I W R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hM
  cases hD
  cases hI
  cases hW
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchySubsequenceExtractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchySubsequenceExtractionUp,
      cauchySubsequenceExtractionFromEventFlow
        (cauchySubsequenceExtractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D I W R H C P N =>
      exact
        congrArg some
          (cauchySubsequenceExtraction_mk_congr
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode S)
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode M)
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode D)
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode I)
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode W)
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode R)
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode H)
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode C)
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode P)
            (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode N))

private theorem cauchySubsequenceExtractionToEventFlow_injective
    {x y : CauchySubsequenceExtractionUp} :
    cauchySubsequenceExtractionToEventFlow x =
      cauchySubsequenceExtractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySubsequenceExtractionFromEventFlow
          (cauchySubsequenceExtractionToEventFlow x) =
        cauchySubsequenceExtractionFromEventFlow
          (cauchySubsequenceExtractionToEventFlow y) :=
    congrArg cauchySubsequenceExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySubsequenceExtractionTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchySubsequenceExtraction_field_faithful :
    ∀ x y : CauchySubsequenceExtractionUp,
      cauchySubsequenceExtractionFields x = cauchySubsequenceExtractionFields y → x = y := by
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
    change
      cauchySubsequenceExtractionFromEventFlow
        (cauchySubsequenceExtractionToEventFlow x) = some x
    exact CauchySubsequenceExtractionTasteGate_single_carrier_alignment_round_trip x
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
          cauchySubsequenceExtractionToEventFlow y → x = y) ∧
      cauchySubsequenceExtractionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchySubsequenceExtractionChapterTasteGate⟩
  constructor
  · exact ⟨cauchySubsequenceExtractionFieldFaithful⟩
  constructor
  · exact ⟨cauchySubsequenceExtractionNontrivial⟩
  constructor
  · exact CauchySubsequenceExtractionTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchySubsequenceExtractionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchySubsequenceExtractionToEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchySubsequenceExtractionUp
