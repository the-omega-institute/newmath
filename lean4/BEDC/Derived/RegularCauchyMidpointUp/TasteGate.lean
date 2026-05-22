import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMidpointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMidpointUp : Type where
  | mk (R0 R1 S0 S1 D Q E H C P N : BHist) : RegularCauchyMidpointUp
  deriving DecidableEq

def regularCauchyMidpointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMidpointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMidpointEncodeBHist h

def regularCauchyMidpointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMidpointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMidpointDecodeBHist tail)

private theorem regularCauchyMidpoint_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyMidpointDecodeBHist (regularCauchyMidpointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem regularCauchyMidpoint_mk_congr
    {R0 R0' R1 R1' S0 S0' S1 S1' D D' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hR0 : R0' = R0) (hR1 : R1' = R1) (hS0 : S0' = S0) (hS1 : S1' = S1)
    (hD : D' = D) (hQ : Q' = Q) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RegularCauchyMidpointUp.mk R0' R1' S0' S1' D' Q' E' H' C' P' N' =
      RegularCauchyMidpointUp.mk R0 R1 S0 S1 D Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR0
  cases hR1
  cases hS0
  cases hS1
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyMidpointFields : RegularCauchyMidpointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMidpointUp.mk R0 R1 S0 S1 D Q E H C P N =>
      [R0, R1, S0, S1, D, Q, E, H, C, P, N]

def regularCauchyMidpointToEventFlow : RegularCauchyMidpointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyMidpointFields x).map regularCauchyMidpointEncodeBHist

def regularCauchyMidpointFromEventFlow : EventFlow → Option RegularCauchyMidpointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R0 :: rest0 =>
      match rest0 with
      | [] => none
      | R1 :: rest1 =>
          match rest1 with
          | [] => none
          | S0 :: rest2 =>
              match rest2 with
              | [] => none
              | S1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
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
                                                    (RegularCauchyMidpointUp.mk
                                                      (regularCauchyMidpointDecodeBHist R0)
                                                      (regularCauchyMidpointDecodeBHist R1)
                                                      (regularCauchyMidpointDecodeBHist S0)
                                                      (regularCauchyMidpointDecodeBHist S1)
                                                      (regularCauchyMidpointDecodeBHist D)
                                                      (regularCauchyMidpointDecodeBHist Q)
                                                      (regularCauchyMidpointDecodeBHist E)
                                                      (regularCauchyMidpointDecodeBHist H)
                                                      (regularCauchyMidpointDecodeBHist C)
                                                      (regularCauchyMidpointDecodeBHist P)
                                                      (regularCauchyMidpointDecodeBHist N))
                                              | _ :: _ => none

private theorem regularCauchyMidpoint_round_trip :
    ∀ x : RegularCauchyMidpointUp,
      regularCauchyMidpointFromEventFlow (regularCauchyMidpointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 S0 S1 D Q E H C P N =>
      exact
        congrArg some
          (regularCauchyMidpoint_mk_congr
            (regularCauchyMidpoint_decode_encode_bhist R0)
            (regularCauchyMidpoint_decode_encode_bhist R1)
            (regularCauchyMidpoint_decode_encode_bhist S0)
            (regularCauchyMidpoint_decode_encode_bhist S1)
            (regularCauchyMidpoint_decode_encode_bhist D)
            (regularCauchyMidpoint_decode_encode_bhist Q)
            (regularCauchyMidpoint_decode_encode_bhist E)
            (regularCauchyMidpoint_decode_encode_bhist H)
            (regularCauchyMidpoint_decode_encode_bhist C)
            (regularCauchyMidpoint_decode_encode_bhist P)
            (regularCauchyMidpoint_decode_encode_bhist N))

private theorem regularCauchyMidpointToEventFlow_injective {x y : RegularCauchyMidpointUp} :
    regularCauchyMidpointToEventFlow x = regularCauchyMidpointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMidpointFromEventFlow (regularCauchyMidpointToEventFlow x) =
        regularCauchyMidpointFromEventFlow (regularCauchyMidpointToEventFlow y) :=
    congrArg regularCauchyMidpointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyMidpoint_round_trip x).symm
      (Eq.trans hread (regularCauchyMidpoint_round_trip y)))

instance regularCauchyMidpointBHistCarrier : BHistCarrier RegularCauchyMidpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMidpointToEventFlow
  fromEventFlow := regularCauchyMidpointFromEventFlow

instance regularCauchyMidpointChapterTasteGate : ChapterTasteGate RegularCauchyMidpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMidpointFromEventFlow (regularCauchyMidpointToEventFlow x) = some x
    exact regularCauchyMidpoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyMidpointToEventFlow_injective heq)

theorem RegularCauchyMidpointTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyMidpointDecodeBHist (regularCauchyMidpointEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyMidpointUp,
        regularCauchyMidpointFromEventFlow (regularCauchyMidpointToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyMidpointUp,
          regularCauchyMidpointToEventFlow x = regularCauchyMidpointToEventFlow y → x = y) ∧
          regularCauchyMidpointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyMidpoint_decode_encode_bhist
  · constructor
    · exact regularCauchyMidpoint_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyMidpointToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyMidpointUp
