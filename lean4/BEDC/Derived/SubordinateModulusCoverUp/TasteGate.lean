import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubordinateModulusCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubordinateModulusCoverUp : Type where
  | mk (tolerance bundle centers radii precision pointwise coverage comparisons transport routes
      provenance nameCert : BHist) : SubordinateModulusCoverUp
  deriving DecidableEq

def subordinateModulusCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subordinateModulusCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subordinateModulusCoverEncodeBHist h

def subordinateModulusCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subordinateModulusCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subordinateModulusCoverDecodeBHist tail)

private theorem subordinateModulusCoverDecode_encode_bhist :
    ∀ h : BHist, subordinateModulusCoverDecodeBHist
      (subordinateModulusCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def subordinateModulusCoverToEventFlow : SubordinateModulusCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise coverage
      comparisons transport routes provenance nameCert =>
      [[BMark.b0],
        subordinateModulusCoverEncodeBHist tolerance,
        [BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist bundle,
        [BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist centers,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist radii,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist precision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist pointwise,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist coverage,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subordinateModulusCoverEncodeBHist comparisons,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subordinateModulusCoverEncodeBHist nameCert]

def subordinateModulusCoverFromEventFlow : EventFlow → Option SubordinateModulusCoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | tolerance :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | bundle :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | centers :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | radii :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | precision :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | pointwise :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | coverage :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | comparisons :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | routes :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | nameCert :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (SubordinateModulusCoverUp.mk
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            tolerance)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            bundle)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            centers)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            radii)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            precision)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            pointwise)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            coverage)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            comparisons)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            transport)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            routes)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            provenance)
                                                                                                          (subordinateModulusCoverDecodeBHist
                                                                                                            nameCert))
                                                                                                  | _ :: _ => none

private theorem subordinateModulusCover_round_trip :
    ∀ x : SubordinateModulusCoverUp,
      subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tolerance bundle centers radii precision pointwise coverage comparisons transport routes
      provenance nameCert =>
      change
        some (SubordinateModulusCoverUp.mk
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist tolerance))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist bundle))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist centers))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist radii))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist precision))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist pointwise))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist coverage))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist comparisons))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist transport))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist routes))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist provenance))
          (subordinateModulusCoverDecodeBHist (subordinateModulusCoverEncodeBHist nameCert))) =
          some (SubordinateModulusCoverUp.mk tolerance bundle centers radii precision pointwise
            coverage comparisons transport routes provenance nameCert)
      rw [subordinateModulusCoverDecode_encode_bhist tolerance,
        subordinateModulusCoverDecode_encode_bhist bundle,
        subordinateModulusCoverDecode_encode_bhist centers,
        subordinateModulusCoverDecode_encode_bhist radii,
        subordinateModulusCoverDecode_encode_bhist precision,
        subordinateModulusCoverDecode_encode_bhist pointwise,
        subordinateModulusCoverDecode_encode_bhist coverage,
        subordinateModulusCoverDecode_encode_bhist comparisons,
        subordinateModulusCoverDecode_encode_bhist transport,
        subordinateModulusCoverDecode_encode_bhist routes,
        subordinateModulusCoverDecode_encode_bhist provenance,
        subordinateModulusCoverDecode_encode_bhist nameCert]

private theorem subordinateModulusCoverToEventFlow_injective {x y : SubordinateModulusCoverUp} :
    subordinateModulusCoverToEventFlow x = subordinateModulusCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow x) =
        subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow y) :=
    congrArg subordinateModulusCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subordinateModulusCover_round_trip x).symm
      (Eq.trans hread (subordinateModulusCover_round_trip y)))

instance subordinateModulusCoverBHistCarrier : BHistCarrier SubordinateModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subordinateModulusCoverToEventFlow
  fromEventFlow := subordinateModulusCoverFromEventFlow

instance subordinateModulusCoverChapterTasteGate : ChapterTasteGate SubordinateModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow x) = some x
    exact subordinateModulusCover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subordinateModulusCoverToEventFlow_injective heq)

theorem SubordinateModulusCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, subordinateModulusCoverDecodeBHist
      (subordinateModulusCoverEncodeBHist h) = h) ∧
      (∀ x : SubordinateModulusCoverUp,
        subordinateModulusCoverFromEventFlow (subordinateModulusCoverToEventFlow x) = some x) ∧
        (∀ x y : SubordinateModulusCoverUp,
          subordinateModulusCoverToEventFlow x = subordinateModulusCoverToEventFlow y → x = y) ∧
          subordinateModulusCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact subordinateModulusCoverDecode_encode_bhist
  · constructor
    · exact subordinateModulusCover_round_trip
    · constructor
      · intro x y heq
        exact subordinateModulusCoverToEventFlow_injective heq
      · rfl

end BEDC.Derived.SubordinateModulusCoverUp
