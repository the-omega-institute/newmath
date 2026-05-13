import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationTimeOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationTimeOrderUp : Type where
  | mk :
      (earlier later retained route gap transports provenance nameCert : BHist) →
      ObservationTimeOrderUp
  deriving DecidableEq

def observationTimeOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationTimeOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationTimeOrderEncodeBHist h

def observationTimeOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationTimeOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationTimeOrderDecodeBHist tail)

private theorem observationTimeOrderDecode_encode_bhist :
    ∀ h : BHist, observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observationTimeOrderToEventFlow : ObservationTimeOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationTimeOrderUp.mk earlier later retained route gap transports provenance nameCert =>
      [[BMark.b0],
        observationTimeOrderEncodeBHist earlier,
        [BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist later,
        [BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist retained,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observationTimeOrderEncodeBHist nameCert]

def observationTimeOrderFromEventFlow : EventFlow → Option ObservationTimeOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | earlier :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | later :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | retained :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gap :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
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
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ObservationTimeOrderUp.mk
                                                                          (observationTimeOrderDecodeBHist
                                                                            earlier)
                                                                          (observationTimeOrderDecodeBHist
                                                                            later)
                                                                          (observationTimeOrderDecodeBHist
                                                                            retained)
                                                                          (observationTimeOrderDecodeBHist
                                                                            route)
                                                                          (observationTimeOrderDecodeBHist
                                                                            gap)
                                                                          (observationTimeOrderDecodeBHist
                                                                            transports)
                                                                          (observationTimeOrderDecodeBHist
                                                                            provenance)
                                                                          (observationTimeOrderDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem observationTimeOrder_round_trip :
    ∀ x : ObservationTimeOrderUp,
      observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk earlier later retained route gap transports provenance nameCert =>
      change
        some
          (ObservationTimeOrderUp.mk
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist earlier))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist later))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist retained))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist route))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist gap))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist transports))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist provenance))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist nameCert))) =
          some
            (ObservationTimeOrderUp.mk earlier later retained route gap transports provenance
              nameCert)
      rw [observationTimeOrderDecode_encode_bhist earlier,
        observationTimeOrderDecode_encode_bhist later,
        observationTimeOrderDecode_encode_bhist retained,
        observationTimeOrderDecode_encode_bhist route,
        observationTimeOrderDecode_encode_bhist gap,
        observationTimeOrderDecode_encode_bhist transports,
        observationTimeOrderDecode_encode_bhist provenance,
        observationTimeOrderDecode_encode_bhist nameCert]

private theorem observationTimeOrderToEventFlow_injective {x y : ObservationTimeOrderUp} :
    observationTimeOrderToEventFlow x = observationTimeOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow x) =
        observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow y) :=
    congrArg observationTimeOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationTimeOrder_round_trip x).symm
      (Eq.trans hread (observationTimeOrder_round_trip y)))

instance observationTimeOrderBHistCarrier : BHistCarrier ObservationTimeOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observationTimeOrderToEventFlow
  fromEventFlow := observationTimeOrderFromEventFlow

instance observationTimeOrderChapterTasteGate : ChapterTasteGate ObservationTimeOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow x) = some x
    exact observationTimeOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationTimeOrderToEventFlow_injective heq)

theorem ObservationTimeOrderTasteGate_single_carrier_alignment :
    (∀ h : BHist, observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist h) = h) ∧
      (∀ x : ObservationTimeOrderUp,
        observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow x) = some x) ∧
        (∀ x y : ObservationTimeOrderUp,
          observationTimeOrderToEventFlow x = observationTimeOrderToEventFlow y → x = y) ∧
          observationTimeOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observationTimeOrderDecode_encode_bhist
  · constructor
    · exact observationTimeOrder_round_trip
    · constructor
      · intro x y heq
        exact observationTimeOrderToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObservationTimeOrderUp
