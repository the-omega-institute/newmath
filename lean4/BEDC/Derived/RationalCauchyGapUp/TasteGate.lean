import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalCauchyGapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalCauchyGapUp : Type where
  | mk (Q D W R E H C P N : BHist) : RationalCauchyGapUp
  deriving DecidableEq

def rationalCauchyGapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalCauchyGapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalCauchyGapEncodeBHist h

def rationalCauchyGapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalCauchyGapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalCauchyGapDecodeBHist tail)

private theorem rationalCauchyGap_decode_encode_bhist :
    ∀ h : BHist, rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem rationalCauchyGap_mk_congr
    {Q Q' D D' W W' R R' E E' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q) (hD : D' = D) (hW : W' = W) (hR : R' = R)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    RationalCauchyGapUp.mk Q' D' W' R' E' H' C' P' N' =
      RationalCauchyGapUp.mk Q D W R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hD
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def rationalCauchyGapFields : RationalCauchyGapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalCauchyGapUp.mk Q D W R E H C P N => [Q, D, W, R, E, H, C, P, N]

def rationalCauchyGapToEventFlow : RationalCauchyGapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalCauchyGapFields x).map rationalCauchyGapEncodeBHist

def rationalCauchyGapFromEventFlow : EventFlow → Option RationalCauchyGapUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Q :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (RationalCauchyGapUp.mk
                                              (rationalCauchyGapDecodeBHist Q)
                                              (rationalCauchyGapDecodeBHist D)
                                              (rationalCauchyGapDecodeBHist W)
                                              (rationalCauchyGapDecodeBHist R)
                                              (rationalCauchyGapDecodeBHist E)
                                              (rationalCauchyGapDecodeBHist H)
                                              (rationalCauchyGapDecodeBHist C)
                                              (rationalCauchyGapDecodeBHist P)
                                              (rationalCauchyGapDecodeBHist N))
                                      | _ :: _ => none

private theorem rationalCauchyGap_round_trip :
    ∀ x : RationalCauchyGapUp,
      rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q D W R E H C P N =>
      exact
        congrArg some
          (rationalCauchyGap_mk_congr
            (rationalCauchyGap_decode_encode_bhist Q)
            (rationalCauchyGap_decode_encode_bhist D)
            (rationalCauchyGap_decode_encode_bhist W)
            (rationalCauchyGap_decode_encode_bhist R)
            (rationalCauchyGap_decode_encode_bhist E)
            (rationalCauchyGap_decode_encode_bhist H)
            (rationalCauchyGap_decode_encode_bhist C)
            (rationalCauchyGap_decode_encode_bhist P)
            (rationalCauchyGap_decode_encode_bhist N))

private theorem rationalCauchyGapToEventFlow_injective {x y : RationalCauchyGapUp} :
    rationalCauchyGapToEventFlow x = rationalCauchyGapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow x) =
        rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow y) :=
    congrArg rationalCauchyGapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rationalCauchyGap_round_trip x).symm
      (Eq.trans hread (rationalCauchyGap_round_trip y)))

instance rationalCauchyGapBHistCarrier : BHistCarrier RationalCauchyGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalCauchyGapToEventFlow
  fromEventFlow := rationalCauchyGapFromEventFlow

instance rationalCauchyGapChapterTasteGate : ChapterTasteGate RationalCauchyGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow x) = some x
    exact rationalCauchyGap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalCauchyGapToEventFlow_injective heq)

namespace TasteGate

theorem RationalCauchyGapTasteGate_single_carrier_alignment :
    (∀ h : BHist, rationalCauchyGapDecodeBHist (rationalCauchyGapEncodeBHist h) = h) ∧
      (∀ x : RationalCauchyGapUp,
        rationalCauchyGapFromEventFlow (rationalCauchyGapToEventFlow x) = some x) ∧
        (∀ x y : RationalCauchyGapUp,
          rationalCauchyGapToEventFlow x = rationalCauchyGapToEventFlow y → x = y) ∧
          rationalCauchyGapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact rationalCauchyGap_decode_encode_bhist
  · constructor
    · exact rationalCauchyGap_round_trip
    · constructor
      · intro x y heq
        exact rationalCauchyGapToEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.RationalCauchyGapUp
