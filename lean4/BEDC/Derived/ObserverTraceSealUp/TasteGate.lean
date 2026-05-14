import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverTraceSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverTraceSealUp : Type where
  | mk :
      (observer trace observation refusal transport route provenance name : BHist) →
      ObserverTraceSealUp
  deriving DecidableEq

private def observerTraceSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerTraceSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerTraceSealEncodeBHist h

private def observerTraceSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerTraceSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerTraceSealDecodeBHist tail)

private theorem observerTraceSealDecode_encode_bhist :
    ∀ h : BHist, observerTraceSealDecodeBHist (observerTraceSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem observerTraceSeal_mk_congr
    {observer observer' trace trace' observation observation' refusal refusal'
      transport transport' route route' provenance provenance' name name' : BHist}
    (hObserver : observer' = observer)
    (hTrace : trace' = trace)
    (hObservation : observation' = observation)
    (hRefusal : refusal' = refusal)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ObserverTraceSealUp.mk observer' trace' observation' refusal' transport' route'
        provenance' name' =
      ObserverTraceSealUp.mk observer trace observation refusal transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hObserver
  cases hTrace
  cases hObservation
  cases hRefusal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

private def observerTraceSealToEventFlow : ObserverTraceSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverTraceSealUp.mk observer trace observation refusal transport route provenance name =>
      [[BMark.b0],
        observerTraceSealEncodeBHist observer,
        [BMark.b1, BMark.b0],
        observerTraceSealEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b0],
        observerTraceSealEncodeBHist observation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerTraceSealEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerTraceSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerTraceSealEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerTraceSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerTraceSealEncodeBHist name]

private def observerTraceSealFromEventFlow : EventFlow → Option ObserverTraceSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observer :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | trace :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | observation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | refusal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ObserverTraceSealUp.mk
                                                                          (observerTraceSealDecodeBHist observer)
                                                                          (observerTraceSealDecodeBHist trace)
                                                                          (observerTraceSealDecodeBHist observation)
                                                                          (observerTraceSealDecodeBHist refusal)
                                                                          (observerTraceSealDecodeBHist transport)
                                                                          (observerTraceSealDecodeBHist route)
                                                                          (observerTraceSealDecodeBHist provenance)
                                                                          (observerTraceSealDecodeBHist name))
                                                                  | _ :: _ => none

private theorem observerTraceSeal_round_trip :
    ∀ x : ObserverTraceSealUp,
      observerTraceSealFromEventFlow (observerTraceSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observer trace observation refusal transport route provenance name =>
      change
        some
          (ObserverTraceSealUp.mk
            (observerTraceSealDecodeBHist (observerTraceSealEncodeBHist observer))
            (observerTraceSealDecodeBHist (observerTraceSealEncodeBHist trace))
            (observerTraceSealDecodeBHist (observerTraceSealEncodeBHist observation))
            (observerTraceSealDecodeBHist (observerTraceSealEncodeBHist refusal))
            (observerTraceSealDecodeBHist (observerTraceSealEncodeBHist transport))
            (observerTraceSealDecodeBHist (observerTraceSealEncodeBHist route))
            (observerTraceSealDecodeBHist (observerTraceSealEncodeBHist provenance))
            (observerTraceSealDecodeBHist (observerTraceSealEncodeBHist name))) =
          some
            (ObserverTraceSealUp.mk observer trace observation refusal transport route
              provenance name)
      exact
        congrArg some
          (observerTraceSeal_mk_congr
            (observerTraceSealDecode_encode_bhist observer)
            (observerTraceSealDecode_encode_bhist trace)
            (observerTraceSealDecode_encode_bhist observation)
            (observerTraceSealDecode_encode_bhist refusal)
            (observerTraceSealDecode_encode_bhist transport)
            (observerTraceSealDecode_encode_bhist route)
            (observerTraceSealDecode_encode_bhist provenance)
            (observerTraceSealDecode_encode_bhist name))

private theorem observerTraceSealToEventFlow_injective {x y : ObserverTraceSealUp} :
    observerTraceSealToEventFlow x = observerTraceSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerTraceSealFromEventFlow (observerTraceSealToEventFlow x) =
        observerTraceSealFromEventFlow (observerTraceSealToEventFlow y) :=
    congrArg observerTraceSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerTraceSeal_round_trip x).symm
      (Eq.trans hread (observerTraceSeal_round_trip y)))

instance observerTraceSealBHistCarrier : BHistCarrier ObserverTraceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerTraceSealToEventFlow
  fromEventFlow := observerTraceSealFromEventFlow

instance observerTraceSealChapterTasteGate : ChapterTasteGate ObserverTraceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerTraceSealFromEventFlow (observerTraceSealToEventFlow x) = some x
    exact observerTraceSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerTraceSealToEventFlow_injective heq)

instance observerTraceSealFieldFaithful : FieldFaithful ObserverTraceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObserverTraceSealUp.mk observer trace observation refusal transport route provenance name =>
        [observer, trace, observation, refusal, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk observer₁ trace₁ observation₁ refusal₁ transport₁ route₁ provenance₁ name₁ =>
      cases y with
      | mk observer₂ trace₂ observation₂ refusal₂ transport₂ route₂ provenance₂ name₂ =>
        injection h with hObserver t1
        injection t1 with hTrace t2
        injection t2 with hObservation t3
        injection t3 with hRefusal t4
        injection t4 with hTransport t5
        injection t5 with hRoute t6
        injection t6 with hProvenance t7
        injection t7 with hName _
        cases hObserver
        cases hTrace
        cases hObservation
        cases hRefusal
        cases hTransport
        cases hRoute
        cases hProvenance
        cases hName
        rfl

def taste_gate : ChapterTasteGate ObserverTraceSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerTraceSealChapterTasteGate

theorem ObserverTraceSealUp_taste_gate_boundary :
    (∀ x : ObserverTraceSealUp, ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
      (∀ (x : ObserverTraceSealUp) (w : RawEvent) (m : BMark),
        List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ChapterTasteGate.no_hidden_input
  · exact ChapterTasteGate.conservativity

end BEDC.Derived.ObserverTraceSealUp
