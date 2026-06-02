import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalRootIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalRootIntervalUp : Type where
  | mk (A L U G B W R S H C P N : BHist) : RationalRootIntervalUp
  deriving DecidableEq

def rationalRootIntervalEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalRootIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalRootIntervalEncodeBHist h

def rationalRootIntervalDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalRootIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalRootIntervalDecodeBHist tail)

theorem RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem rationalRootInterval_mk_congr
    {A A' L L' U U' G G' B B' W W' R R' S S' H H' C C' P P' N N' : BHist}
    (hA : A' = A)
    (hL : L' = L)
    (hU : U' = U)
    (hG : G' = G)
    (hB : B' = B)
    (hW : W' = W)
    (hR : R' = R)
    (hS : S' = S)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    RationalRootIntervalUp.mk A' L' U' G' B' W' R' S' H' C' P' N' =
      RationalRootIntervalUp.mk A L U G B W R S H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hL
  cases hU
  cases hG
  cases hB
  cases hW
  cases hR
  cases hS
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def rationalRootIntervalFields : RationalRootIntervalUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalRootIntervalUp.mk A L U G B W R S H C P N =>
      [A, L, U, G, B, W, R, S, H, C, P, N]

def rationalRootIntervalToEventFlow : RationalRootIntervalUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalRootIntervalFields x).map rationalRootIntervalEncodeBHist

def rationalRootIntervalFromEventFlow : EventFlow -> Option RationalRootIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | G :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | R :: rest6 =>
                              match rest6 with
                              | [] => none
                              | S :: rest7 =>
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
                                                        (RationalRootIntervalUp.mk
                                                          (rationalRootIntervalDecodeBHist A)
                                                          (rationalRootIntervalDecodeBHist L)
                                                          (rationalRootIntervalDecodeBHist U)
                                                          (rationalRootIntervalDecodeBHist G)
                                                          (rationalRootIntervalDecodeBHist B)
                                                          (rationalRootIntervalDecodeBHist W)
                                                          (rationalRootIntervalDecodeBHist R)
                                                          (rationalRootIntervalDecodeBHist S)
                                                          (rationalRootIntervalDecodeBHist H)
                                                          (rationalRootIntervalDecodeBHist C)
                                                          (rationalRootIntervalDecodeBHist P)
                                                          (rationalRootIntervalDecodeBHist N))
                                                  | _ :: _ => none

private theorem rationalRootInterval_round_trip :
    ∀ x : RationalRootIntervalUp,
      rationalRootIntervalFromEventFlow (rationalRootIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A L U G B W R S H C P N =>
      change
        some
          (RationalRootIntervalUp.mk
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist A))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist L))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist U))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist G))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist B))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist W))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist R))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist S))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist H))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist C))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist P))
            (rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist N))) =
          some (RationalRootIntervalUp.mk A L U G B W R S H C P N)
      exact
        congrArg some
          (rationalRootInterval_mk_congr
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode A)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode L)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode U)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode G)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode B)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode W)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode R)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode S)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode H)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode C)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode P)
            (RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode N))

private theorem rationalRootIntervalToEventFlow_injective {x y : RationalRootIntervalUp} :
    rationalRootIntervalToEventFlow x = rationalRootIntervalToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalRootIntervalFromEventFlow (rationalRootIntervalToEventFlow x) =
        rationalRootIntervalFromEventFlow (rationalRootIntervalToEventFlow y) :=
    congrArg rationalRootIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rationalRootInterval_round_trip x).symm
      (Eq.trans hread (rationalRootInterval_round_trip y)))

private theorem rationalRootInterval_fields_faithful :
    ∀ x y : RationalRootIntervalUp, rationalRootIntervalFields x = rationalRootIntervalFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 L1 U1 G1 B1 W1 R1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 L2 U2 G2 B2 W2 R2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance rationalRootIntervalBHistCarrier : BHistCarrier RationalRootIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalRootIntervalToEventFlow
  fromEventFlow := rationalRootIntervalFromEventFlow

instance rationalRootIntervalChapterTasteGate : ChapterTasteGate RationalRootIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalRootIntervalFromEventFlow (rationalRootIntervalToEventFlow x) = some x
    exact rationalRootInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalRootIntervalToEventFlow_injective heq)

instance rationalRootIntervalFieldFaithful : FieldFaithful RationalRootIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalRootIntervalFields
  field_faithful := rationalRootInterval_fields_faithful

instance rationalRootIntervalNontrivial : Nontrivial RationalRootIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalRootIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RationalRootIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem RationalRootIntervalTasteGate_single_carrier_alignment :
    (forall h : BHist, rationalRootIntervalDecodeBHist (rationalRootIntervalEncodeBHist h) = h) ∧
      (forall x : RationalRootIntervalUp,
        rationalRootIntervalFromEventFlow (rationalRootIntervalToEventFlow x) = some x) ∧
        (forall x y : RationalRootIntervalUp,
          rationalRootIntervalToEventFlow x = rationalRootIntervalToEventFlow y -> x = y) ∧
          rationalRootIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RationalRootIntervalTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact rationalRootInterval_round_trip
    · constructor
      · intro x y heq
        exact rationalRootIntervalToEventFlow_injective heq
      · rfl

end BEDC.Derived.RationalRootIntervalUp
