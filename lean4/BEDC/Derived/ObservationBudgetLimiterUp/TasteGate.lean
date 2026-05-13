import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationBudgetLimiterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationBudgetLimiterUp : Type where
  | mk :
      (request budget cap window dyadic readback sealRow transport routes provenance
        nameCert : BHist) →
      ObservationBudgetLimiterUp

def observationBudgetLimiterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationBudgetLimiterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationBudgetLimiterEncodeBHist h

def observationBudgetLimiterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationBudgetLimiterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationBudgetLimiterDecodeBHist tail)

private theorem observationBudgetLimiterDecode_encode_bhist :
    ∀ h : BHist,
      observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observationBudgetLimiterToEventFlow : ObservationBudgetLimiterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationBudgetLimiterUp.mk request budget cap window dyadic readback sealRow transport
      routes provenance nameCert =>
      [[BMark.b0],
        observationBudgetLimiterEncodeBHist request,
        [BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist cap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observationBudgetLimiterEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist nameCert]

def observationBudgetLimiterFromEventFlow : EventFlow → Option ObservationBudgetLimiterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | request :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | budget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cap :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | window :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dyadic :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | readback :: rest11 =>
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
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | provenance ::
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
                                                                                      | nameCert ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ObservationBudgetLimiterUp.mk
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    request)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    budget)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    cap)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    window)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    dyadic)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    readback)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    sealRow)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    transport)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    routes)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    provenance)
                                                                                                  (observationBudgetLimiterDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ ::
                                                                                              _ =>
                                                                                              none

private theorem observationBudgetLimiter_round_trip :
    ∀ x : ObservationBudgetLimiterUp,
      observationBudgetLimiterFromEventFlow (observationBudgetLimiterToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request budget cap window dyadic readback sealRow transport routes provenance nameCert =>
      change
        some
          (ObservationBudgetLimiterUp.mk
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist request))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist budget))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist cap))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist window))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist dyadic))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist readback))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist sealRow))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist transport))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist routes))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist provenance))
            (observationBudgetLimiterDecodeBHist
              (observationBudgetLimiterEncodeBHist nameCert))) =
          some
            (ObservationBudgetLimiterUp.mk request budget cap window dyadic readback sealRow
              transport routes provenance nameCert)
      rw [observationBudgetLimiterDecode_encode_bhist request,
        observationBudgetLimiterDecode_encode_bhist budget,
        observationBudgetLimiterDecode_encode_bhist cap,
        observationBudgetLimiterDecode_encode_bhist window,
        observationBudgetLimiterDecode_encode_bhist dyadic,
        observationBudgetLimiterDecode_encode_bhist readback,
        observationBudgetLimiterDecode_encode_bhist sealRow,
        observationBudgetLimiterDecode_encode_bhist transport,
        observationBudgetLimiterDecode_encode_bhist routes,
        observationBudgetLimiterDecode_encode_bhist provenance,
        observationBudgetLimiterDecode_encode_bhist nameCert]

private theorem observationBudgetLimiterToEventFlow_injective
    {x y : ObservationBudgetLimiterUp} :
    observationBudgetLimiterToEventFlow x = observationBudgetLimiterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observationBudgetLimiterFromEventFlow (observationBudgetLimiterToEventFlow x) =
        observationBudgetLimiterFromEventFlow (observationBudgetLimiterToEventFlow y) :=
    congrArg observationBudgetLimiterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationBudgetLimiter_round_trip x).symm
      (Eq.trans hread (observationBudgetLimiter_round_trip y)))

instance observationBudgetLimiterBHistCarrier : BHistCarrier ObservationBudgetLimiterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observationBudgetLimiterToEventFlow
  fromEventFlow := observationBudgetLimiterFromEventFlow

instance observationBudgetLimiterChapterTasteGate :
    ChapterTasteGate ObservationBudgetLimiterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observationBudgetLimiterFromEventFlow
        (observationBudgetLimiterToEventFlow x) = some x
    exact observationBudgetLimiter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationBudgetLimiterToEventFlow_injective heq)

instance observationBudgetLimiterFieldFaithful :
    FieldFaithful ObservationBudgetLimiterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObservationBudgetLimiterUp.mk request budget cap window dyadic readback sealRow
        transport routes provenance nameCert =>
        [request, budget, cap, window, dyadic, readback, sealRow, transport, routes,
          provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk request₁ budget₁ cap₁ window₁ dyadic₁ readback₁ sealRow₁ transport₁ routes₁
        provenance₁ nameCert₁ =>
        cases y with
        | mk request₂ budget₂ cap₂ window₂ dyadic₂ readback₂ sealRow₂ transport₂ routes₂
            provenance₂ nameCert₂ =>
            cases h
            rfl

def taste_gate : ChapterTasteGate ObservationBudgetLimiterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observationBudgetLimiterChapterTasteGate

theorem ObservationBudgetLimiterTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist h) = h) ∧
      (∀ x : ObservationBudgetLimiterUp,
        observationBudgetLimiterFromEventFlow (observationBudgetLimiterToEventFlow x) =
          some x) ∧
        (∀ x y : ObservationBudgetLimiterUp,
          observationBudgetLimiterToEventFlow x = observationBudgetLimiterToEventFlow y →
            x = y) ∧
          observationBudgetLimiterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observationBudgetLimiterDecode_encode_bhist
  · constructor
    · exact observationBudgetLimiter_round_trip
    · constructor
      · intro x y heq
        exact observationBudgetLimiterToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObservationBudgetLimiterUp
