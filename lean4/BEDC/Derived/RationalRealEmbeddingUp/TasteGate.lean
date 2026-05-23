import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalRealEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalRealEmbeddingUp : Type where
  | mk (Q S R D T H C P N : BHist) : RationalRealEmbeddingUp
  deriving DecidableEq

def rationalRealEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalRealEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalRealEmbeddingEncodeBHist h

def rationalRealEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalRealEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalRealEmbeddingDecodeBHist tail)

private theorem RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem rationalRealEmbeddingEncodeBHist_injective {h k : BHist} :
    rationalRealEmbeddingEncodeBHist h = rationalRealEmbeddingEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist h) =
        rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist k) :=
    congrArg rationalRealEmbeddingDecodeBHist heq
  exact
    Eq.trans
      (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode h).symm
      (Eq.trans hread
        (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode k))

private theorem RationalRealEmbeddingTasteGate_single_carrier_alignment_mk_congr
    {Q1 Q2 S1 S2 R1 R2 D1 D2 T1 T2 H1 H2 C1 C2 P1 P2 N1 N2 : BHist}
    (hQ : Q1 = Q2) (hS : S1 = S2) (hR : R1 = R2) (hD : D1 = D2)
    (hT : T1 = T2) (hH : H1 = H2) (hC : C1 = C2) (hP : P1 = P2)
    (hN : N1 = N2) :
    RationalRealEmbeddingUp.mk Q1 S1 R1 D1 T1 H1 C1 P1 N1 =
      RationalRealEmbeddingUp.mk Q2 S2 R2 D2 T2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hS
  cases hR
  cases hD
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def rationalRealEmbeddingFields : RationalRealEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalRealEmbeddingUp.mk Q S R D T H C P N => [Q, S, R, D, T, H, C, P, N]

def rationalRealEmbeddingToEventFlow : RationalRealEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalRealEmbeddingFields x).map rationalRealEmbeddingEncodeBHist

def rationalRealEmbeddingFromEventFlow : EventFlow → Option RationalRealEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | Q :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
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
                                            (RationalRealEmbeddingUp.mk
                                              (rationalRealEmbeddingDecodeBHist Q)
                                              (rationalRealEmbeddingDecodeBHist S)
                                              (rationalRealEmbeddingDecodeBHist R)
                                              (rationalRealEmbeddingDecodeBHist D)
                                              (rationalRealEmbeddingDecodeBHist T)
                                              (rationalRealEmbeddingDecodeBHist H)
                                              (rationalRealEmbeddingDecodeBHist C)
                                              (rationalRealEmbeddingDecodeBHist P)
                                              (rationalRealEmbeddingDecodeBHist N))
                                      | _ :: _ => none

private theorem RationalRealEmbeddingTasteGate_single_carrier_alignment_round_trip
    (x : RationalRealEmbeddingUp) :
    rationalRealEmbeddingFromEventFlow (rationalRealEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q S R D T H C P N =>
      change
        some
          (RationalRealEmbeddingUp.mk
            (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist Q))
            (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist S))
            (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist R))
            (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist D))
            (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist T))
            (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist H))
            (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist C))
            (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist P))
            (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist N))) =
          some (RationalRealEmbeddingUp.mk Q S R D T H C P N)
      exact
        congrArg some
          (RationalRealEmbeddingTasteGate_single_carrier_alignment_mk_congr
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode Q)
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode S)
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode R)
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode D)
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode T)
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode H)
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode C)
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode P)
            (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode N))

private theorem RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalRealEmbeddingUp} :
    rationalRealEmbeddingToEventFlow x = rationalRealEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalRealEmbeddingFromEventFlow (rationalRealEmbeddingToEventFlow x) =
        rationalRealEmbeddingFromEventFlow (rationalRealEmbeddingToEventFlow y) :=
    congrArg rationalRealEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalRealEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalRealEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

instance rationalRealEmbeddingBHistCarrier : BHistCarrier RationalRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalRealEmbeddingToEventFlow
  fromEventFlow := rationalRealEmbeddingFromEventFlow

instance rationalRealEmbeddingChapterTasteGate :
    ChapterTasteGate RationalRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalRealEmbeddingFromEventFlow (rationalRealEmbeddingToEventFlow x) = some x
    exact RationalRealEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RationalRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RationalRealEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalRealEmbeddingChapterTasteGate

namespace TasteGate

theorem RationalRealEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist, rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist h) = h) ∧
      (∀ x : RationalRealEmbeddingUp,
        rationalRealEmbeddingFromEventFlow (rationalRealEmbeddingToEventFlow x) = some x) ∧
        (∀ x y : RationalRealEmbeddingUp,
          rationalRealEmbeddingToEventFlow x = rationalRealEmbeddingToEventFlow y → x = y) ∧
          rationalRealEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · intro x
      cases x with
      | mk Q S R D T H C P N =>
          change
            some
              (RationalRealEmbeddingUp.mk
                (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist Q))
                (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist S))
                (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist R))
                (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist D))
                (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist T))
                (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist H))
                (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist C))
                (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist P))
                (rationalRealEmbeddingDecodeBHist (rationalRealEmbeddingEncodeBHist N))) =
              some (RationalRealEmbeddingUp.mk Q S R D T H C P N)
          exact
            congrArg some
              (RationalRealEmbeddingTasteGate_single_carrier_alignment_mk_congr
                (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode Q)
                (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode S)
                (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode R)
                (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode D)
                (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode T)
                (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode H)
                (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode C)
                (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode P)
                (RationalRealEmbeddingTasteGate_single_carrier_alignment_decode_encode N))
    · constructor
      · intro x y heq
        cases x with
        | mk Q1 S1 R1 D1 T1 H1 C1 P1 N1 =>
            cases y with
            | mk Q2 S2 R2 D2 T2 H2 C2 P2 N2 =>
                change
                  [rationalRealEmbeddingEncodeBHist Q1, rationalRealEmbeddingEncodeBHist S1,
                      rationalRealEmbeddingEncodeBHist R1, rationalRealEmbeddingEncodeBHist D1,
                      rationalRealEmbeddingEncodeBHist T1, rationalRealEmbeddingEncodeBHist H1,
                      rationalRealEmbeddingEncodeBHist C1, rationalRealEmbeddingEncodeBHist P1,
                      rationalRealEmbeddingEncodeBHist N1] =
                    [rationalRealEmbeddingEncodeBHist Q2, rationalRealEmbeddingEncodeBHist S2,
                      rationalRealEmbeddingEncodeBHist R2, rationalRealEmbeddingEncodeBHist D2,
                      rationalRealEmbeddingEncodeBHist T2, rationalRealEmbeddingEncodeBHist H2,
                      rationalRealEmbeddingEncodeBHist C2, rationalRealEmbeddingEncodeBHist P2,
                      rationalRealEmbeddingEncodeBHist N2] at heq
                injection heq with hQ t1
                injection t1 with hS t2
                injection t2 with hR t3
                injection t3 with hD t4
                injection t4 with hT t5
                injection t5 with hH t6
                injection t6 with hC t7
                injection t7 with hP t8
                injection t8 with hN _
                exact
                  RationalRealEmbeddingTasteGate_single_carrier_alignment_mk_congr
                    (rationalRealEmbeddingEncodeBHist_injective hQ)
                    (rationalRealEmbeddingEncodeBHist_injective hS)
                    (rationalRealEmbeddingEncodeBHist_injective hR)
                    (rationalRealEmbeddingEncodeBHist_injective hD)
                    (rationalRealEmbeddingEncodeBHist_injective hT)
                    (rationalRealEmbeddingEncodeBHist_injective hH)
                    (rationalRealEmbeddingEncodeBHist_injective hC)
                    (rationalRealEmbeddingEncodeBHist_injective hP)
                    (rationalRealEmbeddingEncodeBHist_injective hN)
      · rfl

end TasteGate

end BEDC.Derived.RationalRealEmbeddingUp
