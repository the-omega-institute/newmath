import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyModulusUp : Type where
  | mk : (M S D Q E H C P N : BHist) -> RealCauchyModulusUp
  deriving DecidableEq

def realCauchyModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyModulusEncodeBHist h

def realCauchyModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyModulusDecodeBHist tail)

private theorem realCauchyModulus_decode_encode_bhist :
    forall h : BHist, realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realCauchyModulusEncodeBHist_injective {h k : BHist} :
    realCauchyModulusEncodeBHist h = realCauchyModulusEncodeBHist k -> h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist h) =
        realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist k) :=
    congrArg realCauchyModulusDecodeBHist heq
  exact
    Eq.trans (realCauchyModulus_decode_encode_bhist h).symm
      (Eq.trans hread (realCauchyModulus_decode_encode_bhist k))

private theorem realCauchyModulus_mk_congr
    {M1 M2 S1 S2 D1 D2 Q1 Q2 E1 E2 H1 H2 C1 C2 P1 P2 N1 N2 : BHist}
    (hM : M1 = M2) (hS : S1 = S2) (hD : D1 = D2) (hQ : Q1 = Q2)
    (hE : E1 = E2) (hH : H1 = H2) (hC : C1 = C2) (hP : P1 = P2)
    (hN : N1 = N2) :
    RealCauchyModulusUp.mk M1 S1 D1 Q1 E1 H1 C1 P1 N1 =
      RealCauchyModulusUp.mk M2 S2 D2 Q2 E2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hS
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realCauchyModulusFields : RealCauchyModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyModulusUp.mk M S D Q E H C P N => [M, S, D, Q, E, H, C, P, N]

def realCauchyModulusToEventFlow : RealCauchyModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realCauchyModulusEncodeBHist (realCauchyModulusFields x)

def realCauchyModulusFromEventFlow : EventFlow -> Option RealCauchyModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
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
                                            (RealCauchyModulusUp.mk
                                              (realCauchyModulusDecodeBHist M)
                                              (realCauchyModulusDecodeBHist S)
                                              (realCauchyModulusDecodeBHist D)
                                              (realCauchyModulusDecodeBHist Q)
                                              (realCauchyModulusDecodeBHist E)
                                              (realCauchyModulusDecodeBHist H)
                                              (realCauchyModulusDecodeBHist C)
                                              (realCauchyModulusDecodeBHist P)
                                              (realCauchyModulusDecodeBHist N))
                                      | _ :: _ => none

private theorem realCauchyModulus_round_trip :
    forall x : RealCauchyModulusUp,
      realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S D Q E H C P N =>
      change
        some
          (RealCauchyModulusUp.mk
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist M))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist S))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist D))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist Q))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist E))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist H))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist C))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist P))
            (realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist N))) =
          some (RealCauchyModulusUp.mk M S D Q E H C P N)
      exact
        congrArg some
          (realCauchyModulus_mk_congr
            (realCauchyModulus_decode_encode_bhist M)
            (realCauchyModulus_decode_encode_bhist S)
            (realCauchyModulus_decode_encode_bhist D)
            (realCauchyModulus_decode_encode_bhist Q)
            (realCauchyModulus_decode_encode_bhist E)
            (realCauchyModulus_decode_encode_bhist H)
            (realCauchyModulus_decode_encode_bhist C)
            (realCauchyModulus_decode_encode_bhist P)
            (realCauchyModulus_decode_encode_bhist N))

private theorem realCauchyModulusToEventFlow_injective {x y : RealCauchyModulusUp} :
    realCauchyModulusToEventFlow x = realCauchyModulusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow x) =
        realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow y) :=
    congrArg realCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyModulus_round_trip x).symm
      (Eq.trans hread (realCauchyModulus_round_trip y)))

instance realCauchyModulusBHistCarrier : BHistCarrier RealCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyModulusToEventFlow
  fromEventFlow := realCauchyModulusFromEventFlow

instance realCauchyModulusChapterTasteGate : ChapterTasteGate RealCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow x) = some x
    exact realCauchyModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyModulusToEventFlow_injective heq)

instance realCauchyModulusNontrivial : Nontrivial RealCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCauchyModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCauchyModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCauchyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyModulusChapterTasteGate

theorem RealCauchyModulusTasteGate_single_carrier_alignment :
    (forall h : BHist, realCauchyModulusDecodeBHist (realCauchyModulusEncodeBHist h) = h) ∧
      (forall x : RealCauchyModulusUp,
        realCauchyModulusFromEventFlow (realCauchyModulusToEventFlow x) = some x) ∧
        (forall x y : RealCauchyModulusUp,
          realCauchyModulusToEventFlow x = realCauchyModulusToEventFlow y -> x = y) ∧
          realCauchyModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realCauchyModulus_decode_encode_bhist
  · constructor
    · exact realCauchyModulus_round_trip
    · constructor
      · intro x y heq
        cases x with
        | mk M1 S1 D1 Q1 E1 H1 C1 P1 N1 =>
            cases y with
            | mk M2 S2 D2 Q2 E2 H2 C2 P2 N2 =>
                change
                  [realCauchyModulusEncodeBHist M1, realCauchyModulusEncodeBHist S1,
                      realCauchyModulusEncodeBHist D1, realCauchyModulusEncodeBHist Q1,
                      realCauchyModulusEncodeBHist E1, realCauchyModulusEncodeBHist H1,
                      realCauchyModulusEncodeBHist C1, realCauchyModulusEncodeBHist P1,
                      realCauchyModulusEncodeBHist N1] =
                    [realCauchyModulusEncodeBHist M2, realCauchyModulusEncodeBHist S2,
                      realCauchyModulusEncodeBHist D2, realCauchyModulusEncodeBHist Q2,
                      realCauchyModulusEncodeBHist E2, realCauchyModulusEncodeBHist H2,
                      realCauchyModulusEncodeBHist C2, realCauchyModulusEncodeBHist P2,
                      realCauchyModulusEncodeBHist N2] at heq
                injection heq with hM t1
                injection t1 with hS t2
                injection t2 with hD t3
                injection t3 with hQ t4
                injection t4 with hE t5
                injection t5 with hH t6
                injection t6 with hC t7
                injection t7 with hP t8
                injection t8 with hN _
                exact
                  realCauchyModulus_mk_congr
                    (realCauchyModulusEncodeBHist_injective hM)
                    (realCauchyModulusEncodeBHist_injective hS)
                    (realCauchyModulusEncodeBHist_injective hD)
                    (realCauchyModulusEncodeBHist_injective hQ)
                    (realCauchyModulusEncodeBHist_injective hE)
                    (realCauchyModulusEncodeBHist_injective hH)
                    (realCauchyModulusEncodeBHist_injective hC)
                    (realCauchyModulusEncodeBHist_injective hP)
                    (realCauchyModulusEncodeBHist_injective hN)
      · rfl

end BEDC.Derived.RealCauchyModulusUp
