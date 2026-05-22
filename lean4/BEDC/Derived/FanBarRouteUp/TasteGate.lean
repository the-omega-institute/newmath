import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FanBarRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FanBarRouteUp : Type where
  | mk : (T B I W Q D E H C P N : BHist) → FanBarRouteUp
  deriving DecidableEq

def fanBarRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fanBarRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fanBarRouteEncodeBHist h

def fanBarRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fanBarRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fanBarRouteDecodeBHist tail)

private theorem fanBarRoute_decode_encode_bhist :
    ∀ h : BHist, fanBarRouteDecodeBHist (fanBarRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fanBarRouteToEventFlow : FanBarRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FanBarRouteUp.mk T B I W Q D E H C P N =>
      [[BMark.b0],
        fanBarRouteEncodeBHist T,
        [BMark.b1, BMark.b0],
        fanBarRouteEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        fanBarRouteEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fanBarRouteEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fanBarRouteEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fanBarRouteEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fanBarRouteEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        fanBarRouteEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        fanBarRouteEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        fanBarRouteEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fanBarRouteEncodeBHist N]

def fanBarRouteFromEventFlow : EventFlow → Option FanBarRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | B :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | I :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | W :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | Q :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | D :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | E :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (FanBarRouteUp.mk
                                                                                                  (fanBarRouteDecodeBHist T)
                                                                                                  (fanBarRouteDecodeBHist B)
                                                                                                  (fanBarRouteDecodeBHist I)
                                                                                                  (fanBarRouteDecodeBHist W)
                                                                                                  (fanBarRouteDecodeBHist Q)
                                                                                                  (fanBarRouteDecodeBHist D)
                                                                                                  (fanBarRouteDecodeBHist E)
                                                                                                  (fanBarRouteDecodeBHist H)
                                                                                                  (fanBarRouteDecodeBHist C)
                                                                                                  (fanBarRouteDecodeBHist P)
                                                                                                  (fanBarRouteDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem fanBarRoute_round_trip :
    ∀ x : FanBarRouteUp,
      fanBarRouteFromEventFlow (fanBarRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T B I W Q D E H C P N =>
      change
        some
          (FanBarRouteUp.mk
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist T))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist B))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist I))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist W))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist Q))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist D))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist E))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist H))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist C))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist P))
            (fanBarRouteDecodeBHist (fanBarRouteEncodeBHist N))) =
          some (FanBarRouteUp.mk T B I W Q D E H C P N)
      rw [fanBarRoute_decode_encode_bhist T,
        fanBarRoute_decode_encode_bhist B,
        fanBarRoute_decode_encode_bhist I,
        fanBarRoute_decode_encode_bhist W,
        fanBarRoute_decode_encode_bhist Q,
        fanBarRoute_decode_encode_bhist D,
        fanBarRoute_decode_encode_bhist E,
        fanBarRoute_decode_encode_bhist H,
        fanBarRoute_decode_encode_bhist C,
        fanBarRoute_decode_encode_bhist P,
        fanBarRoute_decode_encode_bhist N]

private theorem fanBarRouteToEventFlow_injective
    {x y : FanBarRouteUp} :
    fanBarRouteToEventFlow x = fanBarRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fanBarRouteFromEventFlow (fanBarRouteToEventFlow x) =
        fanBarRouteFromEventFlow (fanBarRouteToEventFlow y) :=
    congrArg fanBarRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fanBarRoute_round_trip x).symm
      (Eq.trans hread (fanBarRoute_round_trip y)))

instance fanBarRouteBHistCarrier : BHistCarrier FanBarRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fanBarRouteToEventFlow
  fromEventFlow := fanBarRouteFromEventFlow

instance fanBarRouteChapterTasteGate :
    ChapterTasteGate FanBarRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fanBarRouteFromEventFlow (fanBarRouteToEventFlow x) = some x
    exact fanBarRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fanBarRouteToEventFlow_injective heq)

instance fanBarRouteFieldFaithful : FieldFaithful FanBarRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FanBarRouteUp.mk T B I W Q D E H C P N => [T, B, I, W, Q, D, E, H, C, P, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk T1 B1 I1 W1 Q1 D1 E1 H1 C1 P1 N1 =>
        cases y with
        | mk T2 B2 I2 W2 Q2 D2 E2 H2 C2 P2 N2 =>
            injection hfields with hT t1
            cases hT
            injection t1 with hB t2
            cases hB
            injection t2 with hI t3
            cases hI
            injection t3 with hW t4
            cases hW
            injection t4 with hQ t5
            cases hQ
            injection t5 with hD t6
            cases hD
            injection t6 with hE t7
            cases hE
            injection t7 with hH t8
            cases hH
            injection t8 with hC t9
            cases hC
            injection t9 with hP t10
            cases hP
            injection t10 with hN _
            cases hN
            rfl

namespace TasteGate

theorem FanBarRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist, fanBarRouteDecodeBHist (fanBarRouteEncodeBHist h) = h) ∧
      (∀ x : FanBarRouteUp,
        fanBarRouteFromEventFlow (fanBarRouteToEventFlow x) = some x) ∧
        (∀ x y : FanBarRouteUp,
          fanBarRouteToEventFlow x = fanBarRouteToEventFlow y → x = y) ∧
          fanBarRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact fanBarRoute_decode_encode_bhist
  · constructor
    · exact fanBarRoute_round_trip
    · constructor
      · intro x y heq
        exact fanBarRouteToEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.FanBarRouteUp
