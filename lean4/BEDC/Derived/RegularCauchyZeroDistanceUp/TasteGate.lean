import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyZeroDistanceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyZeroDistanceUp : Type where
  | mk (X Y D Z E W T H C P N : BHist) : RegularCauchyZeroDistanceUp
  deriving DecidableEq

def regularCauchyZeroDistanceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyZeroDistanceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyZeroDistanceEncodeBHist h

def regularCauchyZeroDistanceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyZeroDistanceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyZeroDistanceDecodeBHist tail)

private theorem regularCauchyZeroDistance_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyZeroDistanceDecodeBHist (regularCauchyZeroDistanceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem regularCauchyZeroDistance_mk_congr
    {X X' Y Y' D D' Z Z' E E' W W' T T' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hY : Y' = Y) (hD : D' = D) (hZ : Z' = Z)
    (hE : E' = E) (hW : W' = W) (hT : T' = T) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RegularCauchyZeroDistanceUp.mk X' Y' D' Z' E' W' T' H' C' P' N' =
      RegularCauchyZeroDistanceUp.mk X Y D Z E W T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hD
  cases hZ
  cases hE
  cases hW
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyZeroDistanceFields : RegularCauchyZeroDistanceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyZeroDistanceUp.mk X Y D Z E W T H C P N =>
      [X, Y, D, Z, E, W, T, H, C, P, N]

def regularCauchyZeroDistanceToEventFlow : RegularCauchyZeroDistanceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyZeroDistanceFields x).map regularCauchyZeroDistanceEncodeBHist

def regularCauchyZeroDistanceFromEventFlow : EventFlow → Option RegularCauchyZeroDistanceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | Y :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | Z :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | T :: rest6 =>
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
                                                    (RegularCauchyZeroDistanceUp.mk
                                                      (regularCauchyZeroDistanceDecodeBHist X)
                                                      (regularCauchyZeroDistanceDecodeBHist Y)
                                                      (regularCauchyZeroDistanceDecodeBHist D)
                                                      (regularCauchyZeroDistanceDecodeBHist Z)
                                                      (regularCauchyZeroDistanceDecodeBHist E)
                                                      (regularCauchyZeroDistanceDecodeBHist W)
                                                      (regularCauchyZeroDistanceDecodeBHist T)
                                                      (regularCauchyZeroDistanceDecodeBHist H)
                                                      (regularCauchyZeroDistanceDecodeBHist C)
                                                      (regularCauchyZeroDistanceDecodeBHist P)
                                                      (regularCauchyZeroDistanceDecodeBHist N))
                                              | _ :: _ => none

private theorem regularCauchyZeroDistance_round_trip :
    ∀ x : RegularCauchyZeroDistanceUp,
      regularCauchyZeroDistanceFromEventFlow (regularCauchyZeroDistanceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y D Z E W T H C P N =>
      exact
        congrArg some
          (regularCauchyZeroDistance_mk_congr
            (regularCauchyZeroDistance_decode_encode_bhist X)
            (regularCauchyZeroDistance_decode_encode_bhist Y)
            (regularCauchyZeroDistance_decode_encode_bhist D)
            (regularCauchyZeroDistance_decode_encode_bhist Z)
            (regularCauchyZeroDistance_decode_encode_bhist E)
            (regularCauchyZeroDistance_decode_encode_bhist W)
            (regularCauchyZeroDistance_decode_encode_bhist T)
            (regularCauchyZeroDistance_decode_encode_bhist H)
            (regularCauchyZeroDistance_decode_encode_bhist C)
            (regularCauchyZeroDistance_decode_encode_bhist P)
            (regularCauchyZeroDistance_decode_encode_bhist N))

private theorem regularCauchyZeroDistanceToEventFlow_injective
    {x y : RegularCauchyZeroDistanceUp} :
    regularCauchyZeroDistanceToEventFlow x = regularCauchyZeroDistanceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyZeroDistanceFromEventFlow (regularCauchyZeroDistanceToEventFlow x) =
        regularCauchyZeroDistanceFromEventFlow (regularCauchyZeroDistanceToEventFlow y) :=
    congrArg regularCauchyZeroDistanceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyZeroDistance_round_trip x).symm
      (Eq.trans hread (regularCauchyZeroDistance_round_trip y)))

instance regularCauchyZeroDistanceBHistCarrier : BHistCarrier RegularCauchyZeroDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyZeroDistanceToEventFlow
  fromEventFlow := regularCauchyZeroDistanceFromEventFlow

instance regularCauchyZeroDistanceChapterTasteGate :
    ChapterTasteGate RegularCauchyZeroDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyZeroDistanceFromEventFlow (regularCauchyZeroDistanceToEventFlow x) =
      some x
    exact regularCauchyZeroDistance_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyZeroDistanceToEventFlow_injective heq)

theorem RegularCauchyZeroDistanceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyZeroDistanceDecodeBHist (regularCauchyZeroDistanceEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyZeroDistanceUp,
        regularCauchyZeroDistanceFromEventFlow (regularCauchyZeroDistanceToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyZeroDistanceUp,
          regularCauchyZeroDistanceToEventFlow x = regularCauchyZeroDistanceToEventFlow y →
            x = y) ∧
          regularCauchyZeroDistanceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact regularCauchyZeroDistance_decode_encode_bhist
  · constructor
    · exact regularCauchyZeroDistance_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyZeroDistanceToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyZeroDistanceUp
