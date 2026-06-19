import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwartzSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwartzSpaceUp : Type where
  | mk
      (frechet seminormFamily schwartzFunction growthLedger weakDerivative realReadback
        temperedDistribution transport continuation provenance nameCert : BHist) :
      SchwartzSpaceUp
  deriving DecidableEq

def schwartzSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schwartzSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schwartzSpaceEncodeBHist h

def schwartzSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schwartzSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schwartzSpaceDecodeBHist tail)

private theorem schwartzSpaceDecode_encode_bhist :
    ∀ h : BHist, schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schwartzSpaceToEventFlow : SchwartzSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SchwartzSpaceUp.mk frechet seminormFamily schwartzFunction growthLedger weakDerivative
      realReadback temperedDistribution transport continuation provenance nameCert =>
      [[BMark.b0],
        schwartzSpaceEncodeBHist frechet,
        [BMark.b1, BMark.b0],
        schwartzSpaceEncodeBHist seminormFamily,
        [BMark.b1, BMark.b1, BMark.b0],
        schwartzSpaceEncodeBHist schwartzFunction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schwartzSpaceEncodeBHist growthLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schwartzSpaceEncodeBHist weakDerivative,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schwartzSpaceEncodeBHist realReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schwartzSpaceEncodeBHist temperedDistribution,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        schwartzSpaceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        schwartzSpaceEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        schwartzSpaceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schwartzSpaceEncodeBHist nameCert]

def schwartzSpaceFromEventFlow : EventFlow → Option SchwartzSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | frechet :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | seminormFamily :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | schwartzFunction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | growthLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | weakDerivative :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | realReadback :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | temperedDistribution :: rest13 =>
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
                                                                      | continuation :: rest17 =>
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
                                                                                                (SchwartzSpaceUp.mk
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    frechet)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    seminormFamily)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    schwartzFunction)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    growthLedger)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    weakDerivative)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    realReadback)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    temperedDistribution)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    transport)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    continuation)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    provenance)
                                                                                                  (schwartzSpaceDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ => none

private theorem schwartzSpace_round_trip :
    ∀ x : SchwartzSpaceUp,
      schwartzSpaceFromEventFlow (schwartzSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk frechet seminormFamily schwartzFunction growthLedger weakDerivative realReadback
      temperedDistribution transport continuation provenance nameCert =>
      change
        some
          (SchwartzSpaceUp.mk
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist frechet))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist seminormFamily))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist schwartzFunction))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist growthLedger))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist weakDerivative))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist realReadback))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist temperedDistribution))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist transport))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist continuation))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist provenance))
            (schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist nameCert))) =
          some
            (SchwartzSpaceUp.mk frechet seminormFamily schwartzFunction growthLedger
              weakDerivative realReadback temperedDistribution transport continuation provenance
              nameCert)
      rw [schwartzSpaceDecode_encode_bhist frechet,
        schwartzSpaceDecode_encode_bhist seminormFamily,
        schwartzSpaceDecode_encode_bhist schwartzFunction,
        schwartzSpaceDecode_encode_bhist growthLedger,
        schwartzSpaceDecode_encode_bhist weakDerivative,
        schwartzSpaceDecode_encode_bhist realReadback,
        schwartzSpaceDecode_encode_bhist temperedDistribution,
        schwartzSpaceDecode_encode_bhist transport,
        schwartzSpaceDecode_encode_bhist continuation,
        schwartzSpaceDecode_encode_bhist provenance,
        schwartzSpaceDecode_encode_bhist nameCert]

private theorem schwartzSpaceToEventFlow_injective {x y : SchwartzSpaceUp} :
    schwartzSpaceToEventFlow x = schwartzSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schwartzSpaceFromEventFlow (schwartzSpaceToEventFlow x) =
        schwartzSpaceFromEventFlow (schwartzSpaceToEventFlow y) :=
    congrArg schwartzSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (schwartzSpace_round_trip x).symm
      (Eq.trans hread (schwartzSpace_round_trip y)))

instance schwartzSpaceBHistCarrier : BHistCarrier SchwartzSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schwartzSpaceToEventFlow
  fromEventFlow := schwartzSpaceFromEventFlow

instance schwartzSpaceChapterTasteGate : ChapterTasteGate SchwartzSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schwartzSpaceFromEventFlow (schwartzSpaceToEventFlow x) = some x
    exact schwartzSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (schwartzSpaceToEventFlow_injective heq)

theorem SchwartzSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, schwartzSpaceDecodeBHist (schwartzSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SchwartzSpaceUp) ∧
        Nonempty (ChapterTasteGate SchwartzSpaceUp) ∧
          schwartzSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact schwartzSpaceDecode_encode_bhist
  · constructor
    · exact Nonempty.intro inferInstance
    · constructor
      · exact Nonempty.intro inferInstance
      · rfl

end BEDC.Derived.SchwartzSpaceUp
