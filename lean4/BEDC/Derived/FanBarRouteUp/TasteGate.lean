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
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fanBarRouteFields : FanBarRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FanBarRouteUp.mk T B I W Q D E H C P N => [T, B, I, W, Q, D, E, H, C, P, N]

def fanBarRouteToEventFlow : FanBarRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fanBarRouteFields x).map fanBarRouteEncodeBHist

def fanBarRouteFromEventFlow : EventFlow → Option FanBarRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | I :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
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

private theorem fanBarRouteToEventFlow_injective {x y : FanBarRouteUp} :
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

instance fanBarRouteChapterTasteGate : ChapterTasteGate FanBarRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fanBarRouteFromEventFlow (fanBarRouteToEventFlow x) = some x
    exact fanBarRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fanBarRouteToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FanBarRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fanBarRouteChapterTasteGate

theorem FanBarRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist, fanBarRouteDecodeBHist (fanBarRouteEncodeBHist h) = h) ∧
      (∀ x : FanBarRouteUp,
        fanBarRouteFromEventFlow (fanBarRouteToEventFlow x) = some x) ∧
        (∀ x y : FanBarRouteUp,
          fanBarRouteToEventFlow x = fanBarRouteToEventFlow y → x = y) ∧
          fanBarRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨fanBarRoute_decode_encode_bhist,
      fanBarRoute_round_trip,
      (fun _ _ heq => fanBarRouteToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FanBarRouteUp
