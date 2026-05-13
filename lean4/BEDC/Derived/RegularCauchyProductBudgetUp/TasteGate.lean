import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyProductBudgetUp : Type where
  | mk :
      (sourceA sourceB windowA windowB dyadicA dyadicB product budget readback sealRow
        transports routes provenance nameCert : BHist) →
        RegularCauchyProductBudgetUp
  deriving DecidableEq

def regularCauchyProductBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyProductBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyProductBudgetEncodeBHist h

def regularCauchyProductBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyProductBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyProductBudgetDecodeBHist tail)

private theorem regularCauchyProductBudgetDecodeEncodeBHist :
    ∀ h : BHist,
      regularCauchyProductBudgetDecodeBHist
        (regularCauchyProductBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyProductBudgetToEventFlow :
    RegularCauchyProductBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyProductBudgetUp.mk sourceA sourceB windowA windowB dyadicA dyadicB
      product budget readback sealRow transports routes provenance nameCert =>
      [[BMark.b0],
        regularCauchyProductBudgetEncodeBHist sourceA,
        [BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist sourceB,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist windowA,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist windowB,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist dyadicA,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist dyadicB,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist product,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyProductBudgetEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyProductBudgetEncodeBHist nameCert]

def regularCauchyProductBudgetFromEventFlow :
    EventFlow → Option RegularCauchyProductBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceA :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceB :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | windowA :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | windowB :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dyadicA :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | dyadicB :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | product :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | budget :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match
                                                                        rest16
                                                                      with
                                                                      | [] =>
                                                                          none
                                                                      | readback ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | sealRow ::
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
                                                                                      | transports ::
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
                                                                                              | routes ::
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
                                                                                                      | provenance ::
                                                                                                          rest25 =>
                                                                                                          match
                                                                                                            rest25
                                                                                                          with
                                                                                                          | [] =>
                                                                                                              none
                                                                                                          | _tag13 ::
                                                                                                              rest26 =>
                                                                                                              match
                                                                                                                rest26
                                                                                                              with
                                                                                                              | [] =>
                                                                                                                  none
                                                                                                              | nameCert ::
                                                                                                                  rest27 =>
                                                                                                                  match
                                                                                                                    rest27
                                                                                                                  with
                                                                                                                  | [] =>
                                                                                                                      some
                                                                                                                        (RegularCauchyProductBudgetUp.mk
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            sourceA)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            sourceB)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            windowA)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            windowB)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            dyadicA)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            dyadicB)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            product)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            budget)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            readback)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            sealRow)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            transports)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            routes)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            provenance)
                                                                                                                          (regularCauchyProductBudgetDecodeBHist
                                                                                                                            nameCert))
                                                                                                                  | _ :: _ =>
                                                                                                                      none

private theorem regularCauchyProductBudgetRoundTrip :
    ∀ x : RegularCauchyProductBudgetUp,
      regularCauchyProductBudgetFromEventFlow
        (regularCauchyProductBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceA sourceB windowA windowB dyadicA dyadicB product budget readback sealRow
      transports routes provenance nameCert =>
      change
        some
          (RegularCauchyProductBudgetUp.mk
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist sourceA))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist sourceB))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist windowA))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist windowB))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist dyadicA))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist dyadicB))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist product))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist budget))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist readback))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist sealRow))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist transports))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist routes))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist provenance))
            (regularCauchyProductBudgetDecodeBHist
              (regularCauchyProductBudgetEncodeBHist nameCert))) =
          some
            (RegularCauchyProductBudgetUp.mk sourceA sourceB windowA windowB dyadicA
              dyadicB product budget readback sealRow transports routes provenance nameCert)
      rw [regularCauchyProductBudgetDecodeEncodeBHist sourceA,
        regularCauchyProductBudgetDecodeEncodeBHist sourceB,
        regularCauchyProductBudgetDecodeEncodeBHist windowA,
        regularCauchyProductBudgetDecodeEncodeBHist windowB,
        regularCauchyProductBudgetDecodeEncodeBHist dyadicA,
        regularCauchyProductBudgetDecodeEncodeBHist dyadicB,
        regularCauchyProductBudgetDecodeEncodeBHist product,
        regularCauchyProductBudgetDecodeEncodeBHist budget,
        regularCauchyProductBudgetDecodeEncodeBHist readback,
        regularCauchyProductBudgetDecodeEncodeBHist sealRow,
        regularCauchyProductBudgetDecodeEncodeBHist transports,
        regularCauchyProductBudgetDecodeEncodeBHist routes,
        regularCauchyProductBudgetDecodeEncodeBHist provenance,
        regularCauchyProductBudgetDecodeEncodeBHist nameCert]

private theorem regularCauchyProductBudgetToEventFlow_injective
    {x y : RegularCauchyProductBudgetUp} :
    regularCauchyProductBudgetToEventFlow x =
      regularCauchyProductBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyProductBudgetFromEventFlow
          (regularCauchyProductBudgetToEventFlow x) =
        regularCauchyProductBudgetFromEventFlow
          (regularCauchyProductBudgetToEventFlow y) :=
    congrArg regularCauchyProductBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyProductBudgetRoundTrip x).symm
      (Eq.trans hread (regularCauchyProductBudgetRoundTrip y)))

instance regularCauchyProductBudgetBHistCarrier :
    BHistCarrier RegularCauchyProductBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyProductBudgetToEventFlow
  fromEventFlow := regularCauchyProductBudgetFromEventFlow

instance regularCauchyProductBudgetChapterTasteGate :
    ChapterTasteGate RegularCauchyProductBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyProductBudgetFromEventFlow
        (regularCauchyProductBudgetToEventFlow x) = some x
    exact regularCauchyProductBudgetRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyProductBudgetToEventFlow_injective heq)

theorem RegularCauchyProductBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyProductBudgetDecodeBHist
        (regularCauchyProductBudgetEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyProductBudgetUp,
        regularCauchyProductBudgetFromEventFlow
          (regularCauchyProductBudgetToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyProductBudgetUp,
          regularCauchyProductBudgetToEventFlow x =
            regularCauchyProductBudgetToEventFlow y → x = y) ∧
          (∀ (x : RegularCauchyProductBudgetUp) w m,
            List.Mem w (regularCauchyProductBudgetToEventFlow x) →
              List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) ∧
            regularCauchyProductBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyProductBudgetDecodeEncodeBHist
  · constructor
    · intro x
      exact regularCauchyProductBudgetRoundTrip x
    · constructor
      · intro x y heq
        exact regularCauchyProductBudgetToEventFlow_injective heq
      · constructor
        · intro x w m hw hm
          exact BMark_generated_cases m
        · rfl

def taste_gate : (fun _ : BHist => ChapterTasteGate RegularCauchyProductBudgetUp) BHist.Empty :=
  regularCauchyProductBudgetChapterTasteGate

end BEDC.Derived.RegularCauchyProductBudgetUp
