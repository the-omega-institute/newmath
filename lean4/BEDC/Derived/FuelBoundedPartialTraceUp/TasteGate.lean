import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FuelBoundedPartialTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FuelBoundedPartialTraceUp : Type where
  | mk
      (fuel substrate initial tracePrefix readback refusal transport route provenance
        nameCert : BHist) :
      FuelBoundedPartialTraceUp
  deriving DecidableEq

def fuelBoundedPartialTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fuelBoundedPartialTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fuelBoundedPartialTraceEncodeBHist h

def fuelBoundedPartialTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fuelBoundedPartialTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fuelBoundedPartialTraceDecodeBHist tail)

private theorem fuelBoundedPartialTraceDecode_encode_bhist :
    ∀ h : BHist,
      fuelBoundedPartialTraceDecodeBHist
        (fuelBoundedPartialTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem fuelBoundedPartialTrace_mk_congr
    {fuel fuel' substrate substrate' initial initial' tracePrefix tracePrefix'
      readback readback' refusal refusal' transport transport' route route'
      provenance provenance' nameCert nameCert' : BHist}
    (hFuel : fuel' = fuel)
    (hSubstrate : substrate' = substrate)
    (hInitial : initial' = initial)
    (hTracePrefix : tracePrefix' = tracePrefix)
    (hReadback : readback' = readback)
    (hRefusal : refusal' = refusal)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    FuelBoundedPartialTraceUp.mk fuel' substrate' initial' tracePrefix' readback'
        refusal' transport' route' provenance' nameCert' =
      FuelBoundedPartialTraceUp.mk fuel substrate initial tracePrefix readback
        refusal transport route provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hFuel
  cases hSubstrate
  cases hInitial
  cases hTracePrefix
  cases hReadback
  cases hRefusal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

def fuelBoundedPartialTraceToEventFlow :
    FuelBoundedPartialTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FuelBoundedPartialTraceUp.mk fuel substrate initial tracePrefix readback
      refusal transport route provenance nameCert =>
      [[BMark.b0],
        fuelBoundedPartialTraceEncodeBHist fuel,
        [BMark.b1, BMark.b0],
        fuelBoundedPartialTraceEncodeBHist substrate,
        [BMark.b1, BMark.b1, BMark.b0],
        fuelBoundedPartialTraceEncodeBHist initial,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fuelBoundedPartialTraceEncodeBHist tracePrefix,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fuelBoundedPartialTraceEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fuelBoundedPartialTraceEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fuelBoundedPartialTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        fuelBoundedPartialTraceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        fuelBoundedPartialTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        fuelBoundedPartialTraceEncodeBHist nameCert]

def fuelBoundedPartialTraceFromEventFlow :
    EventFlow → Option FuelBoundedPartialTraceUp
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
                      | initial :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tracePrefix :: rest7 =>
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
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (FuelBoundedPartialTraceUp.mk
                                                                                          (fuelBoundedPartialTraceDecodeBHist fuel)
                                                                                          (fuelBoundedPartialTraceDecodeBHist substrate)
                                                                                          (fuelBoundedPartialTraceDecodeBHist initial)
                                                                                          (fuelBoundedPartialTraceDecodeBHist tracePrefix)
                                                                                          (fuelBoundedPartialTraceDecodeBHist readback)
                                                                                          (fuelBoundedPartialTraceDecodeBHist refusal)
                                                                                          (fuelBoundedPartialTraceDecodeBHist transport)
                                                                                          (fuelBoundedPartialTraceDecodeBHist route)
                                                                                          (fuelBoundedPartialTraceDecodeBHist provenance)
                                                                                          (fuelBoundedPartialTraceDecodeBHist nameCert))
                                                                                  | _ :: _ => none

private theorem fuelBoundedPartialTrace_round_trip :
    ∀ x : FuelBoundedPartialTraceUp,
      fuelBoundedPartialTraceFromEventFlow
        (fuelBoundedPartialTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fuel substrate initial tracePrefix readback refusal transport route provenance nameCert =>
      change
        some
          (FuelBoundedPartialTraceUp.mk
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist fuel))
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist substrate))
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist initial))
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist tracePrefix))
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist readback))
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist refusal))
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist transport))
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist route))
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist provenance))
            (fuelBoundedPartialTraceDecodeBHist
              (fuelBoundedPartialTraceEncodeBHist nameCert))) =
          some
            (FuelBoundedPartialTraceUp.mk fuel substrate initial tracePrefix readback
              refusal transport route provenance nameCert)
      exact
        congrArg some
          (fuelBoundedPartialTrace_mk_congr
            (fuelBoundedPartialTraceDecode_encode_bhist fuel)
            (fuelBoundedPartialTraceDecode_encode_bhist substrate)
            (fuelBoundedPartialTraceDecode_encode_bhist initial)
            (fuelBoundedPartialTraceDecode_encode_bhist tracePrefix)
            (fuelBoundedPartialTraceDecode_encode_bhist readback)
            (fuelBoundedPartialTraceDecode_encode_bhist refusal)
            (fuelBoundedPartialTraceDecode_encode_bhist transport)
            (fuelBoundedPartialTraceDecode_encode_bhist route)
            (fuelBoundedPartialTraceDecode_encode_bhist provenance)
            (fuelBoundedPartialTraceDecode_encode_bhist nameCert))

private theorem fuelBoundedPartialTraceToEventFlow_injective
    {x y : FuelBoundedPartialTraceUp} :
    fuelBoundedPartialTraceToEventFlow x =
      fuelBoundedPartialTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fuelBoundedPartialTraceFromEventFlow
          (fuelBoundedPartialTraceToEventFlow x) =
        fuelBoundedPartialTraceFromEventFlow
          (fuelBoundedPartialTraceToEventFlow y) :=
    congrArg fuelBoundedPartialTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fuelBoundedPartialTrace_round_trip x).symm
      (Eq.trans hread (fuelBoundedPartialTrace_round_trip y)))

instance fuelBoundedPartialTraceBHistCarrier :
    BHistCarrier FuelBoundedPartialTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fuelBoundedPartialTraceToEventFlow
  fromEventFlow := fuelBoundedPartialTraceFromEventFlow

instance fuelBoundedPartialTraceChapterTasteGate :
    ChapterTasteGate FuelBoundedPartialTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      fuelBoundedPartialTraceFromEventFlow
        (fuelBoundedPartialTraceToEventFlow x) = some x
    exact fuelBoundedPartialTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fuelBoundedPartialTraceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FuelBoundedPartialTraceUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact fuelBoundedPartialTraceChapterTasteGate

instance fuelBoundedPartialTraceFieldFaithful :
    FieldFaithful FuelBoundedPartialTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FuelBoundedPartialTraceUp.mk fuel substrate initial tracePrefix readback
        refusal transport route provenance nameCert =>
        [fuel, substrate, initial, tracePrefix, readback, refusal, transport, route,
          provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk fuel substrate initial tracePrefix readback refusal transport route provenance nameCert =>
        cases y with
        | mk fuel' substrate' initial' tracePrefix' readback' refusal' transport'
            route' provenance' nameCert' =>
            cases hfields
            rfl

theorem FuelBoundedPartialTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      fuelBoundedPartialTraceDecodeBHist
        (fuelBoundedPartialTraceEncodeBHist h) = h) ∧
      (∀ x : FuelBoundedPartialTraceUp,
        fuelBoundedPartialTraceFromEventFlow
          (fuelBoundedPartialTraceToEventFlow x) = some x) ∧
        (∀ x y : FuelBoundedPartialTraceUp,
          fuelBoundedPartialTraceToEventFlow x =
            fuelBoundedPartialTraceToEventFlow y → x = y) ∧
          fuelBoundedPartialTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact fuelBoundedPartialTraceDecode_encode_bhist
  · constructor
    · exact fuelBoundedPartialTrace_round_trip
    · constructor
      · intro x y heq
        exact fuelBoundedPartialTraceToEventFlow_injective heq
      · rfl

end BEDC.Derived.FuelBoundedPartialTraceUp
