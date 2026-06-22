import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactTotallyBoundedFunctionFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactTotallyBoundedFunctionFamilyUp : Type where
  | mk (X F E B W R V H C P N : BHist) : CompactTotallyBoundedFunctionFamilyUp
  deriving DecidableEq

def compactTotallyBoundedFunctionFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactTotallyBoundedFunctionFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactTotallyBoundedFunctionFamilyEncodeBHist h

def compactTotallyBoundedFunctionFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactTotallyBoundedFunctionFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactTotallyBoundedFunctionFamilyDecodeBHist tail)

private theorem compactTotallyBoundedFunctionFamilyDecodeEncode :
    ∀ h : BHist,
      compactTotallyBoundedFunctionFamilyDecodeBHist
        (compactTotallyBoundedFunctionFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactTotallyBoundedFunctionFamilyFields :
    CompactTotallyBoundedFunctionFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactTotallyBoundedFunctionFamilyUp.mk X F E B W R V H C P N =>
      [X, F, E, B, W, R, V, H, C, P, N]

def compactTotallyBoundedFunctionFamilyToEventFlow :
    CompactTotallyBoundedFunctionFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactTotallyBoundedFunctionFamilyFields x).map
      compactTotallyBoundedFunctionFamilyEncodeBHist

def compactTotallyBoundedFunctionFamilyFromEventFlow :
    EventFlow → Option CompactTotallyBoundedFunctionFamilyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | E :: rest2 =>
              match rest2 with
              | [] => none
              | B :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | V :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CompactTotallyBoundedFunctionFamilyUp.mk
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist X)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist F)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist E)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist B)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist W)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist R)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist V)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist H)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist C)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist P)
                                                      (compactTotallyBoundedFunctionFamilyDecodeBHist N))
                                              | _ :: _ => none

private theorem compactTotallyBoundedFunctionFamily_round_trip :
    ∀ x : CompactTotallyBoundedFunctionFamilyUp,
      compactTotallyBoundedFunctionFamilyFromEventFlow
        (compactTotallyBoundedFunctionFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F E B W R V H C P N =>
      change
        some
          (CompactTotallyBoundedFunctionFamilyUp.mk
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist X))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist F))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist E))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist B))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist W))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist R))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist V))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist H))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist C))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist P))
            (compactTotallyBoundedFunctionFamilyDecodeBHist
              (compactTotallyBoundedFunctionFamilyEncodeBHist N))) =
          some (CompactTotallyBoundedFunctionFamilyUp.mk X F E B W R V H C P N)
      rw [compactTotallyBoundedFunctionFamilyDecodeEncode X,
        compactTotallyBoundedFunctionFamilyDecodeEncode F,
        compactTotallyBoundedFunctionFamilyDecodeEncode E,
        compactTotallyBoundedFunctionFamilyDecodeEncode B,
        compactTotallyBoundedFunctionFamilyDecodeEncode W,
        compactTotallyBoundedFunctionFamilyDecodeEncode R,
        compactTotallyBoundedFunctionFamilyDecodeEncode V,
        compactTotallyBoundedFunctionFamilyDecodeEncode H,
        compactTotallyBoundedFunctionFamilyDecodeEncode C,
        compactTotallyBoundedFunctionFamilyDecodeEncode P,
        compactTotallyBoundedFunctionFamilyDecodeEncode N]

private theorem compactTotallyBoundedFunctionFamilyToEventFlow_injective
    {x y : CompactTotallyBoundedFunctionFamilyUp} :
    compactTotallyBoundedFunctionFamilyToEventFlow x =
      compactTotallyBoundedFunctionFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactTotallyBoundedFunctionFamilyFromEventFlow
          (compactTotallyBoundedFunctionFamilyToEventFlow x) =
        compactTotallyBoundedFunctionFamilyFromEventFlow
          (compactTotallyBoundedFunctionFamilyToEventFlow y) :=
    congrArg compactTotallyBoundedFunctionFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactTotallyBoundedFunctionFamily_round_trip x).symm
      (Eq.trans hread (compactTotallyBoundedFunctionFamily_round_trip y)))

private theorem compactTotallyBoundedFunctionFamily_fields_faithful :
    ∀ x y : CompactTotallyBoundedFunctionFamilyUp,
      compactTotallyBoundedFunctionFamilyFields x =
        compactTotallyBoundedFunctionFamilyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ F₁ E₁ B₁ W₁ R₁ V₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ F₂ E₂ B₂ W₂ R₂ V₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactTotallyBoundedFunctionFamilyBHistCarrier :
    BHistCarrier CompactTotallyBoundedFunctionFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactTotallyBoundedFunctionFamilyToEventFlow
  fromEventFlow := compactTotallyBoundedFunctionFamilyFromEventFlow

instance compactTotallyBoundedFunctionFamilyChapterTasteGate :
    ChapterTasteGate CompactTotallyBoundedFunctionFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactTotallyBoundedFunctionFamilyFromEventFlow
        (compactTotallyBoundedFunctionFamilyToEventFlow x) = some x
    exact compactTotallyBoundedFunctionFamily_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactTotallyBoundedFunctionFamilyToEventFlow_injective heq)

instance compactTotallyBoundedFunctionFamilyFieldFaithful :
    FieldFaithful CompactTotallyBoundedFunctionFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactTotallyBoundedFunctionFamilyFields
  field_faithful := compactTotallyBoundedFunctionFamily_fields_faithful

instance compactTotallyBoundedFunctionFamilyNontrivial :
    Nontrivial CompactTotallyBoundedFunctionFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactTotallyBoundedFunctionFamilyUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CompactTotallyBoundedFunctionFamilyUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactTotallyBoundedFunctionFamilyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactTotallyBoundedFunctionFamilyDecodeBHist
        (compactTotallyBoundedFunctionFamilyEncodeBHist h) = h) ∧
      (∀ x : CompactTotallyBoundedFunctionFamilyUp,
        compactTotallyBoundedFunctionFamilyFromEventFlow
          (compactTotallyBoundedFunctionFamilyToEventFlow x) = some x) ∧
      (∀ x y : CompactTotallyBoundedFunctionFamilyUp,
        compactTotallyBoundedFunctionFamilyToEventFlow x =
          compactTotallyBoundedFunctionFamilyToEventFlow y → x = y) ∧
      compactTotallyBoundedFunctionFamilyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨compactTotallyBoundedFunctionFamilyDecodeEncode,
      compactTotallyBoundedFunctionFamily_round_trip,
      fun _ _ heq => compactTotallyBoundedFunctionFamilyToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CompactTotallyBoundedFunctionFamilyUp
