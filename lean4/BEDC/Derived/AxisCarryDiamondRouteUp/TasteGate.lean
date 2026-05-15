import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisCarryDiamondRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisCarryDiamondRouteUp : Type where
  | mk :
      (overlap carryLeft carryRight normal routeLeft routeRight valueLeft valueRight
        targetLedger boundary continuation provenance nameCert : BHist) →
      AxisCarryDiamondRouteUp
  deriving DecidableEq

def axisCarryDiamondRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisCarryDiamondRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisCarryDiamondRouteEncodeBHist h

def axisCarryDiamondRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisCarryDiamondRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisCarryDiamondRouteDecodeBHist tail)

private theorem axisCarryDiamondRoute_decode_encode_bhist :
    ∀ h : BHist,
      axisCarryDiamondRouteDecodeBHist (axisCarryDiamondRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axisCarryDiamondRouteToEventFlow : AxisCarryDiamondRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisCarryDiamondRouteUp.mk overlap carryLeft carryRight normal routeLeft routeRight
      valueLeft valueRight targetLedger boundary continuation provenance nameCert =>
      [[BMark.b0],
        axisCarryDiamondRouteEncodeBHist overlap,
        [BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist carryLeft,
        [BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist carryRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist normal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist routeLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist routeRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist valueLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axisCarryDiamondRouteEncodeBHist valueRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist targetLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist nameCert]

def axisCarryDiamondRouteFromEventFlow : EventFlow → Option AxisCarryDiamondRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | overlap :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | carryLeft :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | carryRight :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | normal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | routeLeft :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | routeRight :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | valueLeft :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | valueRight :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | targetLedger ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] =>
                                                                                  none
                                                                              | boundary ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | continuation ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | provenance ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      none
                                                                                                  | _tag12 ::
                                                                                                      rest24 =>
                                                                                                      match
                                                                                                        rest24
                                                                                                      with
                                                                                                      | [] =>
                                                                                                          none
                                                                                                      | nameCert ::
                                                                                                          rest25 =>
                                                                                                          match
                                                                                                            rest25
                                                                                                          with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (AxisCarryDiamondRouteUp.mk
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    overlap)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    carryLeft)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    carryRight)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    normal)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    routeLeft)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    routeRight)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    valueLeft)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    valueRight)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    targetLedger)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    boundary)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    continuation)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    provenance)
                                                                                                                  (axisCarryDiamondRouteDecodeBHist
                                                                                                                    nameCert))
                                                                                                          | _ :: _ =>
                                                                                                              none

private theorem axisCarryDiamondRoute_round_trip :
    ∀ x : AxisCarryDiamondRouteUp,
      axisCarryDiamondRouteFromEventFlow (axisCarryDiamondRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk overlap carryLeft carryRight normal routeLeft routeRight valueLeft valueRight
      targetLedger boundary continuation provenance nameCert =>
      change
        some
          (AxisCarryDiamondRouteUp.mk
            (axisCarryDiamondRouteDecodeBHist (axisCarryDiamondRouteEncodeBHist overlap))
            (axisCarryDiamondRouteDecodeBHist (axisCarryDiamondRouteEncodeBHist carryLeft))
            (axisCarryDiamondRouteDecodeBHist
              (axisCarryDiamondRouteEncodeBHist carryRight))
            (axisCarryDiamondRouteDecodeBHist (axisCarryDiamondRouteEncodeBHist normal))
            (axisCarryDiamondRouteDecodeBHist (axisCarryDiamondRouteEncodeBHist routeLeft))
            (axisCarryDiamondRouteDecodeBHist
              (axisCarryDiamondRouteEncodeBHist routeRight))
            (axisCarryDiamondRouteDecodeBHist (axisCarryDiamondRouteEncodeBHist valueLeft))
            (axisCarryDiamondRouteDecodeBHist
              (axisCarryDiamondRouteEncodeBHist valueRight))
            (axisCarryDiamondRouteDecodeBHist
              (axisCarryDiamondRouteEncodeBHist targetLedger))
            (axisCarryDiamondRouteDecodeBHist (axisCarryDiamondRouteEncodeBHist boundary))
            (axisCarryDiamondRouteDecodeBHist
              (axisCarryDiamondRouteEncodeBHist continuation))
            (axisCarryDiamondRouteDecodeBHist
              (axisCarryDiamondRouteEncodeBHist provenance))
            (axisCarryDiamondRouteDecodeBHist (axisCarryDiamondRouteEncodeBHist nameCert))) =
          some
            (AxisCarryDiamondRouteUp.mk overlap carryLeft carryRight normal routeLeft
              routeRight valueLeft valueRight targetLedger boundary continuation provenance
              nameCert)
      rw [axisCarryDiamondRoute_decode_encode_bhist overlap,
        axisCarryDiamondRoute_decode_encode_bhist carryLeft,
        axisCarryDiamondRoute_decode_encode_bhist carryRight,
        axisCarryDiamondRoute_decode_encode_bhist normal,
        axisCarryDiamondRoute_decode_encode_bhist routeLeft,
        axisCarryDiamondRoute_decode_encode_bhist routeRight,
        axisCarryDiamondRoute_decode_encode_bhist valueLeft,
        axisCarryDiamondRoute_decode_encode_bhist valueRight,
        axisCarryDiamondRoute_decode_encode_bhist targetLedger,
        axisCarryDiamondRoute_decode_encode_bhist boundary,
        axisCarryDiamondRoute_decode_encode_bhist continuation,
        axisCarryDiamondRoute_decode_encode_bhist provenance,
        axisCarryDiamondRoute_decode_encode_bhist nameCert]

private theorem axisCarryDiamondRouteToEventFlow_injective
    {x y : AxisCarryDiamondRouteUp} :
    axisCarryDiamondRouteToEventFlow x = axisCarryDiamondRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisCarryDiamondRouteFromEventFlow (axisCarryDiamondRouteToEventFlow x) =
        axisCarryDiamondRouteFromEventFlow (axisCarryDiamondRouteToEventFlow y) :=
    congrArg axisCarryDiamondRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axisCarryDiamondRoute_round_trip x).symm
      (Eq.trans hread (axisCarryDiamondRoute_round_trip y)))

instance axisCarryDiamondRouteBHistCarrier : BHistCarrier AxisCarryDiamondRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisCarryDiamondRouteToEventFlow
  fromEventFlow := axisCarryDiamondRouteFromEventFlow

instance axisCarryDiamondRouteChapterTasteGate :
    ChapterTasteGate AxisCarryDiamondRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axisCarryDiamondRouteFromEventFlow (axisCarryDiamondRouteToEventFlow x) = some x
    exact axisCarryDiamondRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisCarryDiamondRouteToEventFlow_injective heq)

instance axisCarryDiamondRouteFieldFaithful : FieldFaithful AxisCarryDiamondRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AxisCarryDiamondRouteUp.mk overlap carryLeft carryRight normal routeLeft routeRight
        valueLeft valueRight targetLedger boundary continuation provenance nameCert =>
        [overlap, carryLeft, carryRight, normal, routeLeft, routeRight, valueLeft,
          valueRight, targetLedger, boundary, continuation, provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk overlap carryLeft carryRight normal routeLeft routeRight valueLeft valueRight
        targetLedger boundary continuation provenance nameCert =>
        cases y with
        | mk overlap' carryLeft' carryRight' normal' routeLeft' routeRight' valueLeft'
            valueRight' targetLedger' boundary' continuation' provenance' nameCert' =>
            cases hfields
            rfl

instance axisCarryDiamondRouteNontrivial : Nontrivial AxisCarryDiamondRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisCarryDiamondRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AxisCarryDiamondRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxisCarryDiamondRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axisCarryDiamondRouteChapterTasteGate

theorem AxisCarryDiamondRouteTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AxisCarryDiamondRouteUp) ∧
      Nonempty (FieldFaithful AxisCarryDiamondRouteUp) ∧
        Nonempty (Nontrivial AxisCarryDiamondRouteUp) ∧
          (∀ h : BHist,
            axisCarryDiamondRouteDecodeBHist (axisCarryDiamondRouteEncodeBHist h) = h) ∧
            (∀ x : AxisCarryDiamondRouteUp,
              axisCarryDiamondRouteFromEventFlow
                (axisCarryDiamondRouteToEventFlow x) = some x) ∧
              (∀ x y : AxisCarryDiamondRouteUp,
                axisCarryDiamondRouteToEventFlow x =
                  axisCarryDiamondRouteToEventFlow y → x = y) ∧
                axisCarryDiamondRouteEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨axisCarryDiamondRouteChapterTasteGate⟩,
      ⟨axisCarryDiamondRouteFieldFaithful⟩,
      ⟨axisCarryDiamondRouteNontrivial⟩,
      axisCarryDiamondRoute_decode_encode_bhist,
      axisCarryDiamondRoute_round_trip,
      fun x y heq => axisCarryDiamondRouteToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.AxisCarryDiamondRouteUp
