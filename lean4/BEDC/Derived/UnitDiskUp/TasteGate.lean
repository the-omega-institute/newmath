import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UnitDiskUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UnitDiskUp : Type where
  | mk :
      (x y point origin radius bound boundary sameRows route provenance nameCert : BHist) →
        UnitDiskUp

def unitDiskEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: unitDiskEncodeBHist h
  | BHist.e1 h => BMark.b1 :: unitDiskEncodeBHist h

def unitDiskDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (unitDiskDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (unitDiskDecodeBHist tail)

private theorem unitDiskDecode_encode_bhist :
    ∀ h : BHist, unitDiskDecodeBHist (unitDiskEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem unitDisk_mk_congr
    {x x' y y' point point' origin origin' radius radius' bound bound' boundary boundary'
      sameRows sameRows' route route' provenance provenance' nameCert nameCert' : BHist}
    (hX : x' = x)
    (hY : y' = y)
    (hPoint : point' = point)
    (hOrigin : origin' = origin)
    (hRadius : radius' = radius)
    (hBound : bound' = bound)
    (hBoundary : boundary' = boundary)
    (hSameRows : sameRows' = sameRows)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    UnitDiskUp.mk x' y' point' origin' radius' bound' boundary' sameRows' route'
        provenance' nameCert' =
      UnitDiskUp.mk x y point origin radius bound boundary sameRows route provenance
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hPoint
  cases hOrigin
  cases hRadius
  cases hBound
  cases hBoundary
  cases hSameRows
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

def unitDiskToEventFlow : UnitDiskUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UnitDiskUp.mk x y point origin radius bound boundary sameRows route provenance nameCert =>
      [[BMark.b0],
        unitDiskEncodeBHist x,
        [BMark.b1, BMark.b0],
        unitDiskEncodeBHist y,
        [BMark.b1, BMark.b1, BMark.b0],
        unitDiskEncodeBHist point,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitDiskEncodeBHist origin,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitDiskEncodeBHist radius,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitDiskEncodeBHist bound,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitDiskEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        unitDiskEncodeBHist sameRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        unitDiskEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        unitDiskEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitDiskEncodeBHist nameCert]

def unitDiskFromEventFlow : EventFlow → Option UnitDiskUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | x :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | y :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | point :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | origin :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | radius :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | bound :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | boundary :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | sameRows :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | route :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | nameCert ::
                                                                                          rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (UnitDiskUp.mk
                                                                                                  (unitDiskDecodeBHist
                                                                                                    x)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    y)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    point)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    origin)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    radius)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    bound)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    boundary)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    sameRows)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    route)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    provenance)
                                                                                                  (unitDiskDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem unitDisk_round_trip :
    ∀ x : UnitDiskUp, unitDiskFromEventFlow (unitDiskToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk x y point origin radius bound boundary sameRows route provenance nameCert =>
      change
        some
          (UnitDiskUp.mk
            (unitDiskDecodeBHist (unitDiskEncodeBHist x))
            (unitDiskDecodeBHist (unitDiskEncodeBHist y))
            (unitDiskDecodeBHist (unitDiskEncodeBHist point))
            (unitDiskDecodeBHist (unitDiskEncodeBHist origin))
            (unitDiskDecodeBHist (unitDiskEncodeBHist radius))
            (unitDiskDecodeBHist (unitDiskEncodeBHist bound))
            (unitDiskDecodeBHist (unitDiskEncodeBHist boundary))
            (unitDiskDecodeBHist (unitDiskEncodeBHist sameRows))
            (unitDiskDecodeBHist (unitDiskEncodeBHist route))
            (unitDiskDecodeBHist (unitDiskEncodeBHist provenance))
            (unitDiskDecodeBHist (unitDiskEncodeBHist nameCert))) =
          some
            (UnitDiskUp.mk x y point origin radius bound boundary sameRows route provenance
              nameCert)
      exact
        congrArg some
          (unitDisk_mk_congr
            (unitDiskDecode_encode_bhist x)
            (unitDiskDecode_encode_bhist y)
            (unitDiskDecode_encode_bhist point)
            (unitDiskDecode_encode_bhist origin)
            (unitDiskDecode_encode_bhist radius)
            (unitDiskDecode_encode_bhist bound)
            (unitDiskDecode_encode_bhist boundary)
            (unitDiskDecode_encode_bhist sameRows)
            (unitDiskDecode_encode_bhist route)
            (unitDiskDecode_encode_bhist provenance)
            (unitDiskDecode_encode_bhist nameCert))

private theorem unitDiskToEventFlow_injective (x y : UnitDiskUp) :
    unitDiskToEventFlow x = unitDiskToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      unitDiskFromEventFlow (unitDiskToEventFlow x) =
        unitDiskFromEventFlow (unitDiskToEventFlow y) :=
    congrArg unitDiskFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (unitDisk_round_trip x).symm (Eq.trans hread (unitDisk_round_trip y)))

instance unitDiskBHistCarrier : BHistCarrier UnitDiskUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := unitDiskToEventFlow
  fromEventFlow := unitDiskFromEventFlow

instance unitDiskChapterTasteGate : ChapterTasteGate UnitDiskUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change unitDiskFromEventFlow (unitDiskToEventFlow x) = some x
    exact unitDisk_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (unitDiskToEventFlow_injective x y heq)

def taste_gate : ChapterTasteGate UnitDiskUp :=
  -- BEDC touchpoint anchor: BHist BMark
  unitDiskChapterTasteGate

theorem UnitDiskTasteGate_single_carrier_alignment :
    (∀ h : BHist, unitDiskDecodeBHist (unitDiskEncodeBHist h) = h) ∧
      (∀ x : UnitDiskUp, unitDiskFromEventFlow (unitDiskToEventFlow x) = some x) ∧
      (∀ x y : UnitDiskUp, unitDiskToEventFlow x = unitDiskToEventFlow y → x = y) ∧
      unitDiskEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro unitDiskDecode_encode_bhist
      (And.intro unitDisk_round_trip
        (And.intro
          (fun x y heq => unitDiskToEventFlow_injective x y heq)
          rfl))

end BEDC.Derived.UnitDiskUp
