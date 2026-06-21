import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyBracketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyBracketUp : Type where
  | mk (L U D W R I E H C P N : BHist) : LocatedCauchyBracketUp
  deriving DecidableEq

def locatedCauchyBracketEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyBracketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyBracketEncodeBHist h

def locatedCauchyBracketDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyBracketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyBracketDecodeBHist tail)

theorem LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      locatedCauchyBracketDecodeBHist (locatedCauchyBracketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem LocatedCauchyBracketTasteGate_single_carrier_alignment_some_mk
    {L U D W R I E H C P N L' U' D' W' R' I' E' H' C' P' N' : BHist}
    (hL : L' = L) (hU : U' = U) (hD : D' = D) (hW : W' = W) (hR : R' = R)
    (hI : I' = I) (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    some (LocatedCauchyBracketUp.mk L' U' D' W' R' I' E' H' C' P' N') =
      some (LocatedCauchyBracketUp.mk L U D W R I E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hU
  cases hD
  cases hW
  cases hR
  cases hI
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def locatedCauchyBracketFields : LocatedCauchyBracketUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyBracketUp.mk L U D W R I E H C P N => [L, U, D, W, R, I, E, H, C, P, N]

def locatedCauchyBracketToEventFlow : LocatedCauchyBracketUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCauchyBracketFields x).map locatedCauchyBracketEncodeBHist

def locatedCauchyBracketFromEventFlow : EventFlow -> Option LocatedCauchyBracketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: rest0 =>
      match rest0 with
      | [] => none
      | U :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | I :: rest5 =>
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
                                                    (LocatedCauchyBracketUp.mk
                                                      (locatedCauchyBracketDecodeBHist L)
                                                      (locatedCauchyBracketDecodeBHist U)
                                                      (locatedCauchyBracketDecodeBHist D)
                                                      (locatedCauchyBracketDecodeBHist W)
                                                      (locatedCauchyBracketDecodeBHist R)
                                                      (locatedCauchyBracketDecodeBHist I)
                                                      (locatedCauchyBracketDecodeBHist E)
                                                      (locatedCauchyBracketDecodeBHist H)
                                                      (locatedCauchyBracketDecodeBHist C)
                                                      (locatedCauchyBracketDecodeBHist P)
                                                      (locatedCauchyBracketDecodeBHist N))
                                              | _ :: _ => none

theorem LocatedCauchyBracketTasteGate_single_carrier_alignment_round_trip :
    forall x : LocatedCauchyBracketUp,
      locatedCauchyBracketFromEventFlow
        (locatedCauchyBracketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U D W R I E H C P N =>
      exact
        LocatedCauchyBracketTasteGate_single_carrier_alignment_some_mk
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode L)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode U)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode D)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode W)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode R)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode I)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode E)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode H)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode C)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode P)
          (LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode N)

theorem LocatedCauchyBracketTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCauchyBracketUp} :
    locatedCauchyBracketToEventFlow x =
      locatedCauchyBracketToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyBracketFromEventFlow (locatedCauchyBracketToEventFlow x) =
        locatedCauchyBracketFromEventFlow (locatedCauchyBracketToEventFlow y) :=
    congrArg locatedCauchyBracketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCauchyBracketTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCauchyBracketTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCauchyBracketBHistCarrier : BHistCarrier LocatedCauchyBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyBracketToEventFlow
  fromEventFlow := locatedCauchyBracketFromEventFlow

instance locatedCauchyBracketChapterTasteGate : ChapterTasteGate LocatedCauchyBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCauchyBracketFromEventFlow (locatedCauchyBracketToEventFlow x) = some x
    exact LocatedCauchyBracketTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCauchyBracketTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedCauchyBracketTasteGate_single_carrier_alignment :
    (forall h : BHist,
      locatedCauchyBracketDecodeBHist (locatedCauchyBracketEncodeBHist h) = h) /\
      (forall x : LocatedCauchyBracketUp,
        locatedCauchyBracketFromEventFlow
          (locatedCauchyBracketToEventFlow x) = some x) /\
        (forall x y : LocatedCauchyBracketUp,
          locatedCauchyBracketToEventFlow x =
            locatedCauchyBracketToEventFlow y -> x = y) /\
          locatedCauchyBracketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LocatedCauchyBracketTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact LocatedCauchyBracketTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact LocatedCauchyBracketTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.LocatedCauchyBracketUp
