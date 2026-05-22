import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRepresentationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRepresentationUp : Type where
  | mk (S W R D A G H C P E N : BHist) : CauchyRepresentationUp
  deriving DecidableEq

def cauchyRepresentationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRepresentationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRepresentationEncodeBHist h

def cauchyRepresentationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRepresentationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRepresentationDecodeBHist tail)

private theorem cauchyRepresentation_decode_encode_bhist :
    ∀ h : BHist, cauchyRepresentationDecodeBHist (cauchyRepresentationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cauchyRepresentation_mk_congr
    {S S' W W' R R' D D' A A' G G' H H' C C' P P' E E' N N' : BHist}
    (hS : S' = S) (hW : W' = W) (hR : R' = R) (hD : D' = D)
    (hA : A' = A) (hG : G' = G) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hE : E' = E) (hN : N' = N) :
    CauchyRepresentationUp.mk S' W' R' D' A' G' H' C' P' E' N' =
      CauchyRepresentationUp.mk S W R D A G H C P E N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hW
  cases hR
  cases hD
  cases hA
  cases hG
  cases hH
  cases hC
  cases hP
  cases hE
  cases hN
  rfl

def cauchyRepresentationFields : CauchyRepresentationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRepresentationUp.mk S W R D A G H C P E N => [S, W, R, D, A, G, H, C, P, E, N]

def cauchyRepresentationToEventFlow : CauchyRepresentationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRepresentationFields x).map cauchyRepresentationEncodeBHist

def cauchyRepresentationFromEventFlow : EventFlow → Option CauchyRepresentationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | A :: rest4 =>
                      match rest4 with
                      | [] => none
                      | G :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CauchyRepresentationUp.mk
                                                      (cauchyRepresentationDecodeBHist S)
                                                      (cauchyRepresentationDecodeBHist W)
                                                      (cauchyRepresentationDecodeBHist R)
                                                      (cauchyRepresentationDecodeBHist D)
                                                      (cauchyRepresentationDecodeBHist A)
                                                      (cauchyRepresentationDecodeBHist G)
                                                      (cauchyRepresentationDecodeBHist H)
                                                      (cauchyRepresentationDecodeBHist C)
                                                      (cauchyRepresentationDecodeBHist P)
                                                      (cauchyRepresentationDecodeBHist E)
                                                      (cauchyRepresentationDecodeBHist N))
                                              | _ :: _ => none

private theorem cauchyRepresentation_round_trip :
    ∀ x : CauchyRepresentationUp,
      cauchyRepresentationFromEventFlow (cauchyRepresentationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W R D A G H C P E N =>
      exact
        congrArg some
          (cauchyRepresentation_mk_congr
            (cauchyRepresentation_decode_encode_bhist S)
            (cauchyRepresentation_decode_encode_bhist W)
            (cauchyRepresentation_decode_encode_bhist R)
            (cauchyRepresentation_decode_encode_bhist D)
            (cauchyRepresentation_decode_encode_bhist A)
            (cauchyRepresentation_decode_encode_bhist G)
            (cauchyRepresentation_decode_encode_bhist H)
            (cauchyRepresentation_decode_encode_bhist C)
            (cauchyRepresentation_decode_encode_bhist P)
            (cauchyRepresentation_decode_encode_bhist E)
            (cauchyRepresentation_decode_encode_bhist N))

private theorem cauchyRepresentationToEventFlow_injective {x y : CauchyRepresentationUp} :
    cauchyRepresentationToEventFlow x = cauchyRepresentationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRepresentationFromEventFlow (cauchyRepresentationToEventFlow x) =
        cauchyRepresentationFromEventFlow (cauchyRepresentationToEventFlow y) :=
    congrArg cauchyRepresentationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRepresentation_round_trip x).symm
      (Eq.trans hread (cauchyRepresentation_round_trip y)))

instance cauchyRepresentationBHistCarrier : BHistCarrier CauchyRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRepresentationToEventFlow
  fromEventFlow := cauchyRepresentationFromEventFlow

instance cauchyRepresentationChapterTasteGate : ChapterTasteGate CauchyRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRepresentationFromEventFlow (cauchyRepresentationToEventFlow x) = some x
    exact cauchyRepresentation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRepresentationToEventFlow_injective heq)

theorem CauchyRepresentationTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRepresentationDecodeBHist (cauchyRepresentationEncodeBHist h) = h) ∧
      (∀ x : CauchyRepresentationUp,
        cauchyRepresentationFromEventFlow (cauchyRepresentationToEventFlow x) = some x) ∧
        (∀ x y : CauchyRepresentationUp,
          cauchyRepresentationToEventFlow x = cauchyRepresentationToEventFlow y → x = y) ∧
          cauchyRepresentationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyRepresentation_decode_encode_bhist
  · constructor
    · exact cauchyRepresentation_round_trip
    · constructor
      · intro x y heq
        exact cauchyRepresentationToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyRepresentationUp
