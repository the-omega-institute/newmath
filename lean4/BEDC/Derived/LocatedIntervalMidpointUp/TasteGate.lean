import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalMidpointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalMidpointUp : Type where
  | mk (I D E0 E1 B S R Q H C P N : BHist) : LocatedIntervalMidpointUp
  deriving DecidableEq

def locatedIntervalMidpointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalMidpointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalMidpointEncodeBHist h

def locatedIntervalMidpointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalMidpointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalMidpointDecodeBHist tail)

private theorem locatedIntervalMidpoint_decode_encode_bhist :
    ∀ h : BHist,
      locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem locatedIntervalMidpoint_mk_congr
    {I I' D D' E0 E0' E1 E1' B B' S S' R R' Q Q' H H' C C' P P' N N' : BHist}
    (hI : I' = I) (hD : D' = D) (hE0 : E0' = E0) (hE1 : E1' = E1)
    (hB : B' = B) (hS : S' = S) (hR : R' = R) (hQ : Q' = Q)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    LocatedIntervalMidpointUp.mk I' D' E0' E1' B' S' R' Q' H' C' P' N' =
      LocatedIntervalMidpointUp.mk I D E0 E1 B S R Q H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hD
  cases hE0
  cases hE1
  cases hB
  cases hS
  cases hR
  cases hQ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def locatedIntervalMidpointFields : LocatedIntervalMidpointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalMidpointUp.mk I D E0 E1 B S R Q H C P N =>
      [I, D, E0, E1, B, S, R, Q, H, C, P, N]

def locatedIntervalMidpointToEventFlow : LocatedIntervalMidpointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedIntervalMidpointFields x).map locatedIntervalMidpointEncodeBHist

def locatedIntervalMidpointFromEventFlow : EventFlow → Option LocatedIntervalMidpointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | E0 :: rest2 =>
              match rest2 with
              | [] => none
              | E1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Q :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (LocatedIntervalMidpointUp.mk
                                                          (locatedIntervalMidpointDecodeBHist I)
                                                          (locatedIntervalMidpointDecodeBHist D)
                                                          (locatedIntervalMidpointDecodeBHist E0)
                                                          (locatedIntervalMidpointDecodeBHist E1)
                                                          (locatedIntervalMidpointDecodeBHist B)
                                                          (locatedIntervalMidpointDecodeBHist S)
                                                          (locatedIntervalMidpointDecodeBHist R)
                                                          (locatedIntervalMidpointDecodeBHist Q)
                                                          (locatedIntervalMidpointDecodeBHist H)
                                                          (locatedIntervalMidpointDecodeBHist C)
                                                          (locatedIntervalMidpointDecodeBHist P)
                                                          (locatedIntervalMidpointDecodeBHist N))
                                                  | _ :: _ => none

private theorem locatedIntervalMidpoint_round_trip :
    ∀ x : LocatedIntervalMidpointUp,
      locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D E0 E1 B S R Q H C P N =>
      exact
        congrArg some
          (locatedIntervalMidpoint_mk_congr
            (locatedIntervalMidpoint_decode_encode_bhist I)
            (locatedIntervalMidpoint_decode_encode_bhist D)
            (locatedIntervalMidpoint_decode_encode_bhist E0)
            (locatedIntervalMidpoint_decode_encode_bhist E1)
            (locatedIntervalMidpoint_decode_encode_bhist B)
            (locatedIntervalMidpoint_decode_encode_bhist S)
            (locatedIntervalMidpoint_decode_encode_bhist R)
            (locatedIntervalMidpoint_decode_encode_bhist Q)
            (locatedIntervalMidpoint_decode_encode_bhist H)
            (locatedIntervalMidpoint_decode_encode_bhist C)
            (locatedIntervalMidpoint_decode_encode_bhist P)
            (locatedIntervalMidpoint_decode_encode_bhist N))

private theorem locatedIntervalMidpointToEventFlow_injective {x y : LocatedIntervalMidpointUp} :
    locatedIntervalMidpointToEventFlow x = locatedIntervalMidpointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow x) =
        locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow y) :=
    congrArg locatedIntervalMidpointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedIntervalMidpoint_round_trip x).symm
      (Eq.trans hread (locatedIntervalMidpoint_round_trip y)))

instance locatedIntervalMidpointBHistCarrier : BHistCarrier LocatedIntervalMidpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalMidpointToEventFlow
  fromEventFlow := locatedIntervalMidpointFromEventFlow

instance locatedIntervalMidpointChapterTasteGate : ChapterTasteGate LocatedIntervalMidpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow x) = some x
    exact locatedIntervalMidpoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedIntervalMidpointToEventFlow_injective heq)

theorem LocatedIntervalMidpointTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist h) = h) ∧
      (∀ x : LocatedIntervalMidpointUp,
        locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow x) = some x) ∧
        (∀ x y : LocatedIntervalMidpointUp,
          locatedIntervalMidpointToEventFlow x = locatedIntervalMidpointToEventFlow y → x = y) ∧
          locatedIntervalMidpointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact locatedIntervalMidpoint_decode_encode_bhist
  · constructor
    · exact locatedIntervalMidpoint_round_trip
    · constructor
      · intro x y heq
        exact locatedIntervalMidpointToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocatedIntervalMidpointUp
