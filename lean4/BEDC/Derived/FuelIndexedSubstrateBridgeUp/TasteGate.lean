import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FuelIndexedSubstrateBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FuelIndexedSubstrateBridgeUp : Type where
  | mk
      (fuel substrateState totalEvaluator finiteWindow readback refusal transport route
        provenance nameCert : BHist) :
      FuelIndexedSubstrateBridgeUp
  deriving DecidableEq

def fuelIndexedSubstrateBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fuelIndexedSubstrateBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fuelIndexedSubstrateBridgeEncodeBHist h

def fuelIndexedSubstrateBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fuelIndexedSubstrateBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fuelIndexedSubstrateBridgeDecodeBHist tail)

private theorem fuelIndexedSubstrateBridgeDecode_encode_bhist :
    ∀ h : BHist,
      fuelIndexedSubstrateBridgeDecodeBHist
        (fuelIndexedSubstrateBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fuelIndexedSubstrateBridgeToEventFlow :
    FuelIndexedSubstrateBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FuelIndexedSubstrateBridgeUp.mk fuel substrateState totalEvaluator finiteWindow readback
      refusal transport route provenance nameCert =>
      [[BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist fuel,
        [BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist substrateState,
        [BMark.b1, BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist totalEvaluator,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist finiteWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist nameCert]

def fuelIndexedSubstrateBridgeFromEventFlow :
    EventFlow → Option FuelIndexedSubstrateBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | fuel :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | substrateState :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | totalEvaluator :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | finiteWindow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | refusal :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
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
                                                                              | nameCert ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      some
                                                                                        (FuelIndexedSubstrateBridgeUp.mk
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            fuel)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            substrateState)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            totalEvaluator)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            finiteWindow)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            readback)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            refusal)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            transport)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            route)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            provenance)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem fuelIndexedSubstrateBridge_round_trip :
    ∀ x : FuelIndexedSubstrateBridgeUp,
      fuelIndexedSubstrateBridgeFromEventFlow
        (fuelIndexedSubstrateBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fuel substrateState totalEvaluator finiteWindow readback refusal transport route
      provenance nameCert =>
      change
        some
          (FuelIndexedSubstrateBridgeUp.mk
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist fuel))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist substrateState))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist totalEvaluator))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist finiteWindow))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist readback))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist refusal))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist transport))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist route))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist provenance))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist nameCert))) =
          some
            (FuelIndexedSubstrateBridgeUp.mk fuel substrateState totalEvaluator finiteWindow
              readback refusal transport route provenance nameCert)
      rw [fuelIndexedSubstrateBridgeDecode_encode_bhist fuel,
        fuelIndexedSubstrateBridgeDecode_encode_bhist substrateState,
        fuelIndexedSubstrateBridgeDecode_encode_bhist totalEvaluator,
        fuelIndexedSubstrateBridgeDecode_encode_bhist finiteWindow,
        fuelIndexedSubstrateBridgeDecode_encode_bhist readback,
        fuelIndexedSubstrateBridgeDecode_encode_bhist refusal,
        fuelIndexedSubstrateBridgeDecode_encode_bhist transport,
        fuelIndexedSubstrateBridgeDecode_encode_bhist route,
        fuelIndexedSubstrateBridgeDecode_encode_bhist provenance,
        fuelIndexedSubstrateBridgeDecode_encode_bhist nameCert]

private theorem fuelIndexedSubstrateBridgeToEventFlow_injective
    {x y : FuelIndexedSubstrateBridgeUp} :
    fuelIndexedSubstrateBridgeToEventFlow x =
      fuelIndexedSubstrateBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fuelIndexedSubstrateBridgeFromEventFlow
          (fuelIndexedSubstrateBridgeToEventFlow x) =
        fuelIndexedSubstrateBridgeFromEventFlow
          (fuelIndexedSubstrateBridgeToEventFlow y) :=
    congrArg fuelIndexedSubstrateBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fuelIndexedSubstrateBridge_round_trip x).symm
      (Eq.trans hread (fuelIndexedSubstrateBridge_round_trip y)))

private def fuelIndexedSubstrateBridgeFields :
    FuelIndexedSubstrateBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FuelIndexedSubstrateBridgeUp.mk fuel substrateState totalEvaluator finiteWindow readback
      refusal transport route provenance nameCert =>
      [fuel, substrateState, totalEvaluator, finiteWindow, readback, refusal, transport, route,
        provenance, nameCert]

private theorem fuelIndexedSubstrateBridge_field_faithful :
    ∀ x y : FuelIndexedSubstrateBridgeUp,
      fuelIndexedSubstrateBridgeFields x = fuelIndexedSubstrateBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk fuel substrateState totalEvaluator finiteWindow readback refusal transport route
      provenance nameCert =>
      cases y with
      | mk fuel' substrateState' totalEvaluator' finiteWindow' readback' refusal' transport'
          route' provenance' nameCert' =>
          cases hfields
          rfl

instance fuelIndexedSubstrateBridgeBHistCarrier :
    BHistCarrier FuelIndexedSubstrateBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fuelIndexedSubstrateBridgeToEventFlow
  fromEventFlow := fuelIndexedSubstrateBridgeFromEventFlow

instance fuelIndexedSubstrateBridgeChapterTasteGate :
    ChapterTasteGate FuelIndexedSubstrateBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      fuelIndexedSubstrateBridgeFromEventFlow
        (fuelIndexedSubstrateBridgeToEventFlow x) = some x
    exact fuelIndexedSubstrateBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fuelIndexedSubstrateBridgeToEventFlow_injective heq)

instance fuelIndexedSubstrateBridgeFieldFaithful :
    FieldFaithful FuelIndexedSubstrateBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fuelIndexedSubstrateBridgeFields
  field_faithful := fuelIndexedSubstrateBridge_field_faithful

instance fuelIndexedSubstrateBridgeNontrivial :
    Nontrivial FuelIndexedSubstrateBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FuelIndexedSubstrateBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FuelIndexedSubstrateBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FuelIndexedSubstrateBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fuelIndexedSubstrateBridgeChapterTasteGate

theorem FuelIndexedSubstrateBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      fuelIndexedSubstrateBridgeDecodeBHist
        (fuelIndexedSubstrateBridgeEncodeBHist h) = h) ∧
      (∀ x : FuelIndexedSubstrateBridgeUp,
        fuelIndexedSubstrateBridgeFromEventFlow
          (fuelIndexedSubstrateBridgeToEventFlow x) = some x) ∧
        (∀ x y : FuelIndexedSubstrateBridgeUp,
          fuelIndexedSubstrateBridgeToEventFlow x =
            fuelIndexedSubstrateBridgeToEventFlow y → x = y) ∧
          fuelIndexedSubstrateBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨fuelIndexedSubstrateBridgeDecode_encode_bhist, fuelIndexedSubstrateBridge_round_trip,
      (fun _ _ heq => fuelIndexedSubstrateBridgeToEventFlow_injective heq), rfl⟩

end BEDC.Derived.FuelIndexedSubstrateBridgeUp
