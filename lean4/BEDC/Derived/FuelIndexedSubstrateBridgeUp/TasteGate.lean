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
      (fuel substrate evaluator window readback refusal transport route provenance name : BHist) :
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

private theorem fuelIndexedSubstrateBridge_mk_congr
    {fuel fuel' substrate substrate' evaluator evaluator' window window' readback readback'
      refusal refusal' transport transport' route route' provenance provenance' name name' : BHist}
    (hFuel : fuel' = fuel)
    (hSubstrate : substrate' = substrate)
    (hEvaluator : evaluator' = evaluator)
    (hWindow : window' = window)
    (hReadback : readback' = readback)
    (hRefusal : refusal' = refusal)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    FuelIndexedSubstrateBridgeUp.mk fuel' substrate' evaluator' window' readback' refusal'
        transport' route' provenance' name' =
      FuelIndexedSubstrateBridgeUp.mk fuel substrate evaluator window readback refusal transport
        route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hFuel
  cases hSubstrate
  cases hEvaluator
  cases hWindow
  cases hReadback
  cases hRefusal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def fuelIndexedSubstrateBridgeToEventFlow :
    FuelIndexedSubstrateBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FuelIndexedSubstrateBridgeUp.mk fuel substrate evaluator window readback refusal transport
      route provenance name =>
      [[BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist fuel,
        [BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist substrate,
        [BMark.b1, BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist evaluator,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fuelIndexedSubstrateBridgeEncodeBHist window,
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
        fuelIndexedSubstrateBridgeEncodeBHist name]

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
              | substrate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | evaluator :: rest5 =>
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
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match
                                                                        rest16
                                                                      with
                                                                      | [] =>
                                                                          none
                                                                      | provenance ::
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
                                                                              | name ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (FuelIndexedSubstrateBridgeUp.mk
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            fuel)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            substrate)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            evaluator)
                                                                                          (fuelIndexedSubstrateBridgeDecodeBHist
                                                                                            window)
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
                                                                                            name))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem fuelIndexedSubstrateBridge_round_trip :
    ∀ x : FuelIndexedSubstrateBridgeUp,
      fuelIndexedSubstrateBridgeFromEventFlow
        (fuelIndexedSubstrateBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fuel substrate evaluator window readback refusal transport route provenance name =>
      change
        some
          (FuelIndexedSubstrateBridgeUp.mk
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist fuel))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist substrate))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist evaluator))
            (fuelIndexedSubstrateBridgeDecodeBHist
              (fuelIndexedSubstrateBridgeEncodeBHist window))
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
              (fuelIndexedSubstrateBridgeEncodeBHist name))) =
          some
            (FuelIndexedSubstrateBridgeUp.mk fuel substrate evaluator window readback
              refusal transport route provenance name)
      exact
        congrArg some
          (fuelIndexedSubstrateBridge_mk_congr
            (fuelIndexedSubstrateBridgeDecode_encode_bhist fuel)
            (fuelIndexedSubstrateBridgeDecode_encode_bhist substrate)
            (fuelIndexedSubstrateBridgeDecode_encode_bhist evaluator)
            (fuelIndexedSubstrateBridgeDecode_encode_bhist window)
            (fuelIndexedSubstrateBridgeDecode_encode_bhist readback)
            (fuelIndexedSubstrateBridgeDecode_encode_bhist refusal)
            (fuelIndexedSubstrateBridgeDecode_encode_bhist transport)
            (fuelIndexedSubstrateBridgeDecode_encode_bhist route)
            (fuelIndexedSubstrateBridgeDecode_encode_bhist provenance)
            (fuelIndexedSubstrateBridgeDecode_encode_bhist name))

private theorem fuelIndexedSubstrateBridgeToEventFlow_injective
    {x y : FuelIndexedSubstrateBridgeUp} :
    fuelIndexedSubstrateBridgeToEventFlow x =
      fuelIndexedSubstrateBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk fuel₁ substrate₁ evaluator₁ window₁ readback₁ refusal₁ transport₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk fuel₂ substrate₂ evaluator₂ window₂ readback₂ refusal₂ transport₂ route₂
          provenance₂ name₂ =>
          injection heq with _ htail1
          injection htail1 with hfuel htail2
          injection htail2 with _ htail3
          injection htail3 with hsubstrate htail4
          injection htail4 with _ htail5
          injection htail5 with hevaluator htail6
          injection htail6 with _ htail7
          injection htail7 with hwindow htail8
          injection htail8 with _ htail9
          injection htail9 with hreadback htail10
          injection htail10 with _ htail11
          injection htail11 with hrefusal htail12
          injection htail12 with _ htail13
          injection htail13 with htransport htail14
          injection htail14 with _ htail15
          injection htail15 with hroute htail16
          injection htail16 with _ htail17
          injection htail17 with hprovenance htail18
          injection htail18 with _ htail19
          injection htail19 with hname _
          have hfuelDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist fuel₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist fuel₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist hfuel
          have hsubstrateDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist substrate₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist substrate₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist hsubstrate
          have hevaluatorDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist evaluator₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist evaluator₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist hevaluator
          have hwindowDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist window₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist window₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist hwindow
          have hreadbackDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist readback₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist readback₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist hreadback
          have hrefusalDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist refusal₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist refusal₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist hrefusal
          have htransportDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist transport₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist transport₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist htransport
          have hrouteDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist route₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist route₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist hroute
          have hprovenanceDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist provenance₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist provenance₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist hprovenance
          have hnameDecoded :
              fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist name₁) =
                fuelIndexedSubstrateBridgeDecodeBHist
                  (fuelIndexedSubstrateBridgeEncodeBHist name₂) :=
            congrArg fuelIndexedSubstrateBridgeDecodeBHist hname
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist fuel₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist fuel₂] at hfuelDecoded
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist substrate₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist substrate₂] at hsubstrateDecoded
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist evaluator₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist evaluator₂] at hevaluatorDecoded
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist window₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist window₂] at hwindowDecoded
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist readback₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist readback₂] at hreadbackDecoded
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist refusal₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist refusal₂] at hrefusalDecoded
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist transport₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist transport₂] at htransportDecoded
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist route₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist route₂] at hrouteDecoded
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist provenance₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist provenance₂] at hprovenanceDecoded
          rw [fuelIndexedSubstrateBridgeDecode_encode_bhist name₁,
            fuelIndexedSubstrateBridgeDecode_encode_bhist name₂] at hnameDecoded
          cases hfuelDecoded
          cases hsubstrateDecoded
          cases hevaluatorDecoded
          cases hwindowDecoded
          cases hreadbackDecoded
          cases hrefusalDecoded
          cases htransportDecoded
          cases hrouteDecoded
          cases hprovenanceDecoded
          cases hnameDecoded
          rfl

instance fuelIndexedSubstrateBridgeBHistCarrier :
    BHistCarrier FuelIndexedSubstrateBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fuelIndexedSubstrateBridgeToEventFlow
  fromEventFlow := fuelIndexedSubstrateBridgeFromEventFlow

instance taste_gate :
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

instance fuelIndexedSubstrateBridgeNontrivial :
    Nontrivial FuelIndexedSubstrateBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FuelIndexedSubstrateBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FuelIndexedSubstrateBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

instance fuelIndexedSubstrateBridgeFieldFaithful :
    FieldFaithful FuelIndexedSubstrateBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FuelIndexedSubstrateBridgeUp.mk fuel substrate evaluator window readback refusal
        transport route provenance name =>
        [fuel, substrate, evaluator, window, readback, refusal, transport, route,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk fuel₁ substrate₁ evaluator₁ window₁ readback₁ refusal₁ transport₁ route₁
        provenance₁ name₁ =>
        cases y with
        | mk fuel₂ substrate₂ evaluator₂ window₂ readback₂ refusal₂ transport₂ route₂
            provenance₂ name₂ =>
            injection h with hfuel t1
            injection t1 with hsubstrate t2
            injection t2 with hevaluator t3
            injection t3 with hwindow t4
            injection t4 with hreadback t5
            injection t5 with hrefusal t6
            injection t6 with htransport t7
            injection t7 with hroute t8
            injection t8 with hprovenance t9
            injection t9 with hname _
            cases hfuel
            cases hsubstrate
            cases hevaluator
            cases hwindow
            cases hreadback
            cases hrefusal
            cases htransport
            cases hroute
            cases hprovenance
            cases hname
            rfl

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
  constructor
  · exact fuelIndexedSubstrateBridgeDecode_encode_bhist
  · constructor
    · exact fuelIndexedSubstrateBridge_round_trip
    · constructor
      · intro x y heq
        exact fuelIndexedSubstrateBridgeToEventFlow_injective heq
      · rfl

end BEDC.Derived.FuelIndexedSubstrateBridgeUp
