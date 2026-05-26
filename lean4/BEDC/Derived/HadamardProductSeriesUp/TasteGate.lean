import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HadamardProductSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HadamardProductSeriesUp : Type where
  | mk : (A B W D R S M E H C P N : BHist) -> HadamardProductSeriesUp
  deriving DecidableEq

def hadamardProductSeriesEncodeBHist : BHist -> List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hadamardProductSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hadamardProductSeriesEncodeBHist h

def hadamardProductSeriesDecodeBHist : List BMark -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hadamardProductSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hadamardProductSeriesDecodeBHist tail)

private theorem hadamardProductSeriesDecodeEncode :
    forall h : BHist,
      hadamardProductSeriesDecodeBHist (hadamardProductSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hadamardProductSeriesFields : HadamardProductSeriesUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HadamardProductSeriesUp.mk A B W D R S M E H C P N =>
      [A, B, W, D, R, S, M, E, H, C, P, N]

def hadamardProductSeriesToEventFlow : HadamardProductSeriesUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hadamardProductSeriesFields x).map hadamardProductSeriesEncodeBHist

def hadamardProductSeriesFromEventFlow :
    EventFlow -> Option HadamardProductSeriesUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | S :: rest5 =>
                          match rest5 with
                          | [] => none
                          | M :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
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
                                                        (HadamardProductSeriesUp.mk
                                                          (hadamardProductSeriesDecodeBHist A)
                                                          (hadamardProductSeriesDecodeBHist B)
                                                          (hadamardProductSeriesDecodeBHist W)
                                                          (hadamardProductSeriesDecodeBHist D)
                                                          (hadamardProductSeriesDecodeBHist R)
                                                          (hadamardProductSeriesDecodeBHist S)
                                                          (hadamardProductSeriesDecodeBHist M)
                                                          (hadamardProductSeriesDecodeBHist E)
                                                          (hadamardProductSeriesDecodeBHist H)
                                                          (hadamardProductSeriesDecodeBHist C)
                                                          (hadamardProductSeriesDecodeBHist P)
                                                          (hadamardProductSeriesDecodeBHist N))
                                                  | _ :: _ => none

private theorem hadamardProductSeriesMkCongr
    {A A' B B' W W' D D' R R' S S' M M' E E' H H' C C' P P' N N' : BHist}
    (hA : A = A') (hB : B = B') (hW : W = W') (hD : D = D') (hR : R = R')
    (hS : S = S') (hM : M = M') (hE : E = E') (hH : H = H') (hC : C = C')
    (hP : P = P') (hN : N = N') :
    HadamardProductSeriesUp.mk A B W D R S M E H C P N =
      HadamardProductSeriesUp.mk A' B' W' D' R' S' M' E' H' C' P' N' := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hB
  cases hW
  cases hD
  cases hR
  cases hS
  cases hM
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem hadamardProductSeriesRoundTrip :
    forall x : HadamardProductSeriesUp,
      hadamardProductSeriesFromEventFlow (hadamardProductSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B W D R S M E H C P N =>
      exact
        congrArg Option.some
          (hadamardProductSeriesMkCongr
            (hadamardProductSeriesDecodeEncode A)
            (hadamardProductSeriesDecodeEncode B)
            (hadamardProductSeriesDecodeEncode W)
            (hadamardProductSeriesDecodeEncode D)
            (hadamardProductSeriesDecodeEncode R)
            (hadamardProductSeriesDecodeEncode S)
            (hadamardProductSeriesDecodeEncode M)
            (hadamardProductSeriesDecodeEncode E)
            (hadamardProductSeriesDecodeEncode H)
            (hadamardProductSeriesDecodeEncode C)
            (hadamardProductSeriesDecodeEncode P)
            (hadamardProductSeriesDecodeEncode N))

private theorem hadamardProductSeriesToEventFlow_injective
    {x y : HadamardProductSeriesUp} :
    hadamardProductSeriesToEventFlow x = hadamardProductSeriesToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hadamardProductSeriesFromEventFlow (hadamardProductSeriesToEventFlow x) =
        hadamardProductSeriesFromEventFlow (hadamardProductSeriesToEventFlow y) :=
    congrArg hadamardProductSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hadamardProductSeriesRoundTrip x).symm
      (Eq.trans hread (hadamardProductSeriesRoundTrip y)))

instance hadamardProductSeriesBHistCarrier : BHistCarrier HadamardProductSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hadamardProductSeriesToEventFlow
  fromEventFlow := hadamardProductSeriesFromEventFlow

instance hadamardProductSeriesChapterTasteGate :
    ChapterTasteGate HadamardProductSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hadamardProductSeriesFromEventFlow (hadamardProductSeriesToEventFlow x) = some x
    exact hadamardProductSeriesRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hadamardProductSeriesToEventFlow_injective heq)

theorem HadamardProductSeriesTasteGate_single_carrier_alignment :
    (forall h : BHist,
      hadamardProductSeriesDecodeBHist (hadamardProductSeriesEncodeBHist h) = h) ∧
      (forall x : HadamardProductSeriesUp,
        hadamardProductSeriesFromEventFlow (hadamardProductSeriesToEventFlow x) = some x) ∧
        (forall x y : HadamardProductSeriesUp,
          hadamardProductSeriesToEventFlow x = hadamardProductSeriesToEventFlow y -> x = y) ∧
          hadamardProductSeriesEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact hadamardProductSeriesDecodeEncode
  · constructor
    · exact hadamardProductSeriesRoundTrip
    · constructor
      · intro x y heq
        exact hadamardProductSeriesToEventFlow_injective heq
      · rfl

end BEDC.Derived.HadamardProductSeriesUp
