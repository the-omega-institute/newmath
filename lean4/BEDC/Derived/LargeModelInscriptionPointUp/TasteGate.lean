import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelInscriptionPointUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelInscriptionPointUp : Type where
  | mk : (model prompt output boundary transport routes provenance nameCert : BHist) →
      LargeModelInscriptionPointUp
  deriving DecidableEq

def largeModelInscriptionPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: largeModelInscriptionPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: largeModelInscriptionPointEncodeBHist h

def largeModelInscriptionPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (largeModelInscriptionPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (largeModelInscriptionPointDecodeBHist tail)

private theorem largeModelInscriptionPointDecode_encode_bhist :
    ∀ h : BHist,
      largeModelInscriptionPointDecodeBHist
        (largeModelInscriptionPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def largeModelInscriptionPointToEventFlow :
    LargeModelInscriptionPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelInscriptionPointUp.mk model prompt output boundary transport routes provenance
      nameCert =>
      [[BMark.b0], largeModelInscriptionPointEncodeBHist model, [BMark.b1, BMark.b0],
        largeModelInscriptionPointEncodeBHist prompt, [BMark.b1, BMark.b1, BMark.b0],
        largeModelInscriptionPointEncodeBHist output,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelInscriptionPointEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelInscriptionPointEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelInscriptionPointEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelInscriptionPointEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        largeModelInscriptionPointEncodeBHist nameCert]

def largeModelInscriptionPointFromEventFlow :
    EventFlow → Option LargeModelInscriptionPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | model :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | prompt :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | output :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | boundary :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | routes :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (LargeModelInscriptionPointUp.mk
                                                                          (largeModelInscriptionPointDecodeBHist
                                                                            model)
                                                                          (largeModelInscriptionPointDecodeBHist
                                                                            prompt)
                                                                          (largeModelInscriptionPointDecodeBHist
                                                                            output)
                                                                          (largeModelInscriptionPointDecodeBHist
                                                                            boundary)
                                                                          (largeModelInscriptionPointDecodeBHist
                                                                            transport)
                                                                          (largeModelInscriptionPointDecodeBHist
                                                                            routes)
                                                                          (largeModelInscriptionPointDecodeBHist
                                                                            provenance)
                                                                          (largeModelInscriptionPointDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem largeModelInscriptionPoint_round_trip :
    ∀ x : LargeModelInscriptionPointUp,
      largeModelInscriptionPointFromEventFlow
        (largeModelInscriptionPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk model prompt output boundary transport routes provenance nameCert =>
      change
        some
          (LargeModelInscriptionPointUp.mk
            (largeModelInscriptionPointDecodeBHist
              (largeModelInscriptionPointEncodeBHist model))
            (largeModelInscriptionPointDecodeBHist
              (largeModelInscriptionPointEncodeBHist prompt))
            (largeModelInscriptionPointDecodeBHist
              (largeModelInscriptionPointEncodeBHist output))
            (largeModelInscriptionPointDecodeBHist
              (largeModelInscriptionPointEncodeBHist boundary))
            (largeModelInscriptionPointDecodeBHist
              (largeModelInscriptionPointEncodeBHist transport))
            (largeModelInscriptionPointDecodeBHist
              (largeModelInscriptionPointEncodeBHist routes))
            (largeModelInscriptionPointDecodeBHist
              (largeModelInscriptionPointEncodeBHist provenance))
            (largeModelInscriptionPointDecodeBHist
              (largeModelInscriptionPointEncodeBHist nameCert))) =
          some
            (LargeModelInscriptionPointUp.mk model prompt output boundary transport routes
              provenance nameCert)
      rw [largeModelInscriptionPointDecode_encode_bhist model,
        largeModelInscriptionPointDecode_encode_bhist prompt,
        largeModelInscriptionPointDecode_encode_bhist output,
        largeModelInscriptionPointDecode_encode_bhist boundary,
        largeModelInscriptionPointDecode_encode_bhist transport,
        largeModelInscriptionPointDecode_encode_bhist routes,
        largeModelInscriptionPointDecode_encode_bhist provenance,
        largeModelInscriptionPointDecode_encode_bhist nameCert]

private theorem largeModelInscriptionPointToEventFlow_injective
    {x y : LargeModelInscriptionPointUp} :
    largeModelInscriptionPointToEventFlow x =
      largeModelInscriptionPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelInscriptionPointFromEventFlow
          (largeModelInscriptionPointToEventFlow x) =
        largeModelInscriptionPointFromEventFlow
          (largeModelInscriptionPointToEventFlow y) :=
    congrArg largeModelInscriptionPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelInscriptionPoint_round_trip x).symm
      (Eq.trans hread (largeModelInscriptionPoint_round_trip y)))

instance largeModelInscriptionPointBHistCarrier :
    BHistCarrier LargeModelInscriptionPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelInscriptionPointToEventFlow
  fromEventFlow := largeModelInscriptionPointFromEventFlow

instance largeModelInscriptionPointChapterTasteGate :
    ChapterTasteGate LargeModelInscriptionPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      largeModelInscriptionPointFromEventFlow
        (largeModelInscriptionPointToEventFlow x) = some x
    exact largeModelInscriptionPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelInscriptionPointToEventFlow_injective heq)

instance largeModelInscriptionPointFieldFaithful :
    FieldFaithful LargeModelInscriptionPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LargeModelInscriptionPointUp.mk model prompt output boundary transport routes provenance
        nameCert =>
        [model, prompt, output, boundary, transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk model₁ prompt₁ output₁ boundary₁ transport₁ routes₁ provenance₁ nameCert₁ =>
        cases y with
        | mk model₂ prompt₂ output₂ boundary₂ transport₂ routes₂ provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

instance largeModelInscriptionPointNontrivial :
    Nontrivial LargeModelInscriptionPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LargeModelInscriptionPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LargeModelInscriptionPointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LargeModelInscriptionPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  largeModelInscriptionPointChapterTasteGate

theorem LargeModelInscriptionPointTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      largeModelInscriptionPointDecodeBHist
        (largeModelInscriptionPointEncodeBHist h) = h) ∧
      (∀ x : LargeModelInscriptionPointUp,
        largeModelInscriptionPointFromEventFlow
          (largeModelInscriptionPointToEventFlow x) = some x) ∧
        (∀ x y : LargeModelInscriptionPointUp,
          largeModelInscriptionPointToEventFlow x =
            largeModelInscriptionPointToEventFlow y → x = y) ∧
          largeModelInscriptionPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact largeModelInscriptionPointDecode_encode_bhist
  · constructor
    · exact largeModelInscriptionPoint_round_trip
    · constructor
      · intro x y heq
        exact largeModelInscriptionPointToEventFlow_injective heq
      · rfl

end BEDC.Derived.LargeModelInscriptionPointUp.TasteGate
