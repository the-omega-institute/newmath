import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDiagonalFusionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDiagonalFusionUp : Type where
  | mk :
      (source diagonal cofinal tail schedule fusion sealRow transport routes provenance
        nameCert : BHist) →
      CauchyDiagonalFusionUp
  deriving DecidableEq

def cauchyDiagonalFusionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDiagonalFusionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDiagonalFusionEncodeBHist h

def cauchyDiagonalFusionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDiagonalFusionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDiagonalFusionDecodeBHist tail)

private theorem cauchyDiagonalFusionDecode_encode_bhist :
    ∀ h : BHist,
      cauchyDiagonalFusionDecodeBHist (cauchyDiagonalFusionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyDiagonalFusionToEventFlow : CauchyDiagonalFusionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDiagonalFusionUp.mk source diagonal cofinal tail schedule fusion sealRow transport
      routes provenance nameCert =>
      [[BMark.b0],
        cauchyDiagonalFusionEncodeBHist source,
        [BMark.b1, BMark.b0],
        cauchyDiagonalFusionEncodeBHist diagonal,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyDiagonalFusionEncodeBHist cofinal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyDiagonalFusionEncodeBHist tail,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyDiagonalFusionEncodeBHist schedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyDiagonalFusionEncodeBHist fusion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyDiagonalFusionEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyDiagonalFusionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyDiagonalFusionEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyDiagonalFusionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyDiagonalFusionEncodeBHist nameCert]

def cauchyDiagonalFusionFromEventFlow : EventFlow → Option CauchyDiagonalFusionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | diagonal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cofinal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tail :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | schedule :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | fusion :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | sealRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | routes :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | nameCert :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CauchyDiagonalFusionUp.mk
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    source)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    diagonal)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    cofinal)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    tail)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    schedule)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    fusion)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    sealRow)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    transport)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    routes)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    provenance)
                                                                                                  (cauchyDiagonalFusionDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ => none

private theorem cauchyDiagonalFusion_round_trip :
    ∀ x : CauchyDiagonalFusionUp,
      cauchyDiagonalFusionFromEventFlow
        (cauchyDiagonalFusionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source diagonal cofinal tail schedule fusion sealRow transport routes provenance nameCert =>
      change
        some
          (CauchyDiagonalFusionUp.mk
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist source))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist diagonal))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist cofinal))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist tail))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist schedule))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist fusion))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist sealRow))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist transport))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist routes))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist provenance))
            (cauchyDiagonalFusionDecodeBHist
              (cauchyDiagonalFusionEncodeBHist nameCert))) =
          some
            (CauchyDiagonalFusionUp.mk source diagonal cofinal tail schedule fusion sealRow
              transport routes provenance nameCert)
      rw [cauchyDiagonalFusionDecode_encode_bhist source,
        cauchyDiagonalFusionDecode_encode_bhist diagonal,
        cauchyDiagonalFusionDecode_encode_bhist cofinal,
        cauchyDiagonalFusionDecode_encode_bhist tail,
        cauchyDiagonalFusionDecode_encode_bhist schedule,
        cauchyDiagonalFusionDecode_encode_bhist fusion,
        cauchyDiagonalFusionDecode_encode_bhist sealRow,
        cauchyDiagonalFusionDecode_encode_bhist transport,
        cauchyDiagonalFusionDecode_encode_bhist routes,
        cauchyDiagonalFusionDecode_encode_bhist provenance,
        cauchyDiagonalFusionDecode_encode_bhist nameCert]

private theorem cauchyDiagonalFusionToEventFlow_injective {x y : CauchyDiagonalFusionUp} :
    cauchyDiagonalFusionToEventFlow x = cauchyDiagonalFusionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDiagonalFusionFromEventFlow (cauchyDiagonalFusionToEventFlow x) =
        cauchyDiagonalFusionFromEventFlow (cauchyDiagonalFusionToEventFlow y) :=
    congrArg cauchyDiagonalFusionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyDiagonalFusion_round_trip x).symm
      (Eq.trans hread (cauchyDiagonalFusion_round_trip y)))

instance cauchyDiagonalFusionBHistCarrier : BHistCarrier CauchyDiagonalFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDiagonalFusionToEventFlow
  fromEventFlow := cauchyDiagonalFusionFromEventFlow

instance cauchyDiagonalFusionChapterTasteGate :
    ChapterTasteGate CauchyDiagonalFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyDiagonalFusionFromEventFlow (cauchyDiagonalFusionToEventFlow x) = some x
    exact cauchyDiagonalFusion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyDiagonalFusionToEventFlow_injective heq)

instance cauchyDiagonalFusionFieldFaithful : FieldFaithful CauchyDiagonalFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CauchyDiagonalFusionUp.mk source diagonal cofinal tail schedule fusion sealRow transport
        routes provenance nameCert =>
        [source, diagonal, cofinal, tail, schedule, fusion, sealRow, transport, routes,
          provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ diagonal₁ cofinal₁ tail₁ schedule₁ fusion₁ sealRow₁ transport₁ routes₁
        provenance₁ nameCert₁ =>
        cases y with
        | mk source₂ diagonal₂ cofinal₂ tail₂ schedule₂ fusion₂ sealRow₂ transport₂ routes₂
            provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

def taste_gate : ChapterTasteGate CauchyDiagonalFusionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyDiagonalFusionChapterTasteGate

theorem CauchyDiagonalFusionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyDiagonalFusionDecodeBHist (cauchyDiagonalFusionEncodeBHist h) = h) ∧
      (∀ x : CauchyDiagonalFusionUp,
        cauchyDiagonalFusionFromEventFlow (cauchyDiagonalFusionToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyDiagonalFusionUp,
          cauchyDiagonalFusionToEventFlow x = cauchyDiagonalFusionToEventFlow y →
            x = y) ∧
          cauchyDiagonalFusionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyDiagonalFusionDecode_encode_bhist
  · constructor
    · exact cauchyDiagonalFusion_round_trip
    · constructor
      · intro x y heq
        exact cauchyDiagonalFusionToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyDiagonalFusionUp
