import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRemainderEstimateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRemainderEstimateUp : Type where
  | mk (S D T W R B H C P N : BHist) : CauchyRemainderEstimateUp

def cauchyRemainderEstimateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRemainderEstimateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRemainderEstimateEncodeBHist h

def cauchyRemainderEstimateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRemainderEstimateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRemainderEstimateDecodeBHist tail)

private theorem cauchyRemainderEstimate_decode_encode_bhist :
    ∀ h : BHist,
      cauchyRemainderEstimateDecodeBHist
        (cauchyRemainderEstimateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyRemainderEstimate_mk_congr
    {S S' D D' T T' W W' R R' B B' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hD : D' = D) (hT : T' = T) (hW : W' = W)
    (hR : R' = R) (hB : B' = B) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyRemainderEstimateUp.mk S' D' T' W' R' B' H' C' P' N' =
      CauchyRemainderEstimateUp.mk S D T W R B H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hD
  cases hT
  cases hW
  cases hR
  cases hB
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyRemainderEstimateFields : CauchyRemainderEstimateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRemainderEstimateUp.mk S D T W R B H C P N =>
      [S, D, T, W, R, B, H, C, P, N]

def cauchyRemainderEstimateToEventFlow : CauchyRemainderEstimateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRemainderEstimateUp.mk S D T W R B H C P N =>
      [cauchyRemainderEstimateEncodeBHist S,
        cauchyRemainderEstimateEncodeBHist D,
        cauchyRemainderEstimateEncodeBHist T,
        cauchyRemainderEstimateEncodeBHist W,
        cauchyRemainderEstimateEncodeBHist R,
        cauchyRemainderEstimateEncodeBHist B,
        cauchyRemainderEstimateEncodeBHist H,
        cauchyRemainderEstimateEncodeBHist C,
        cauchyRemainderEstimateEncodeBHist P,
        cauchyRemainderEstimateEncodeBHist N]

def cauchyRemainderEstimateFromEventFlow :
    EventFlow → Option CauchyRemainderEstimateUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | D :: restD =>
          match restD with
          | T :: restT =>
              match restT with
              | W :: restW =>
                  match restW with
                  | R :: restR =>
                      match restR with
                      | B :: restB =>
                          match restB with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (CauchyRemainderEstimateUp.mk
                                                  (cauchyRemainderEstimateDecodeBHist S)
                                                  (cauchyRemainderEstimateDecodeBHist D)
                                                  (cauchyRemainderEstimateDecodeBHist T)
                                                  (cauchyRemainderEstimateDecodeBHist W)
                                                  (cauchyRemainderEstimateDecodeBHist R)
                                                  (cauchyRemainderEstimateDecodeBHist B)
                                                  (cauchyRemainderEstimateDecodeBHist H)
                                                  (cauchyRemainderEstimateDecodeBHist C)
                                                  (cauchyRemainderEstimateDecodeBHist P)
                                                  (cauchyRemainderEstimateDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem cauchyRemainderEstimate_round_trip :
    ∀ x : CauchyRemainderEstimateUp,
      cauchyRemainderEstimateFromEventFlow
        (cauchyRemainderEstimateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D T W R B H C P N =>
      change
        some
          (CauchyRemainderEstimateUp.mk
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist S))
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist D))
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist T))
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist W))
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist R))
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist B))
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist H))
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist C))
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist P))
            (cauchyRemainderEstimateDecodeBHist (cauchyRemainderEstimateEncodeBHist N))) =
          some (CauchyRemainderEstimateUp.mk S D T W R B H C P N)
      exact
        congrArg some
          (cauchyRemainderEstimate_mk_congr
            (cauchyRemainderEstimate_decode_encode_bhist S)
            (cauchyRemainderEstimate_decode_encode_bhist D)
            (cauchyRemainderEstimate_decode_encode_bhist T)
            (cauchyRemainderEstimate_decode_encode_bhist W)
            (cauchyRemainderEstimate_decode_encode_bhist R)
            (cauchyRemainderEstimate_decode_encode_bhist B)
            (cauchyRemainderEstimate_decode_encode_bhist H)
            (cauchyRemainderEstimate_decode_encode_bhist C)
            (cauchyRemainderEstimate_decode_encode_bhist P)
            (cauchyRemainderEstimate_decode_encode_bhist N))

private theorem cauchyRemainderEstimateToEventFlow_injective
    {x y : CauchyRemainderEstimateUp} :
    cauchyRemainderEstimateToEventFlow x =
      cauchyRemainderEstimateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRemainderEstimateFromEventFlow
          (cauchyRemainderEstimateToEventFlow x) =
        cauchyRemainderEstimateFromEventFlow
          (cauchyRemainderEstimateToEventFlow y) :=
    congrArg cauchyRemainderEstimateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRemainderEstimate_round_trip x).symm
      (Eq.trans hread (cauchyRemainderEstimate_round_trip y)))

instance cauchyRemainderEstimateBHistCarrier :
    BHistCarrier CauchyRemainderEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRemainderEstimateToEventFlow
  fromEventFlow := cauchyRemainderEstimateFromEventFlow

instance cauchyRemainderEstimateChapterTasteGate :
    ChapterTasteGate CauchyRemainderEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyRemainderEstimateFromEventFlow
        (cauchyRemainderEstimateToEventFlow x) = some x
    exact cauchyRemainderEstimate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRemainderEstimateToEventFlow_injective heq)

theorem CauchyRemainderEstimateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyRemainderEstimateDecodeBHist
        (cauchyRemainderEstimateEncodeBHist h) = h) ∧
      (∀ x : CauchyRemainderEstimateUp,
        cauchyRemainderEstimateFromEventFlow
          (cauchyRemainderEstimateToEventFlow x) = some x) ∧
        (∀ x y : CauchyRemainderEstimateUp,
          cauchyRemainderEstimateToEventFlow x =
            cauchyRemainderEstimateToEventFlow y → x = y) ∧
          cauchyRemainderEstimateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyRemainderEstimate_decode_encode_bhist
  · constructor
    · exact cauchyRemainderEstimate_round_trip
    · constructor
      · intro x y heq
        exact cauchyRemainderEstimateToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyRemainderEstimateUp
