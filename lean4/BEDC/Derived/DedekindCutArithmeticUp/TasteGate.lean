import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCutArithmeticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCutArithmeticUp : Type where
  | mk (D L U Q S R E O H C P N : BHist) : DedekindCutArithmeticUp
  deriving DecidableEq

def dedekindCutArithmeticEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCutArithmeticEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCutArithmeticEncodeBHist h

def dedekindCutArithmeticDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCutArithmeticDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCutArithmeticDecodeBHist tail)

private theorem dedekindCutArithmeticDecode_encode_bhist :
    ∀ h : BHist,
      dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem dedekindCutArithmetic_mk_congr
    {D D' L L' U U' Q Q' S S' R R' E E' O O' H H' C C' P P' N N' : BHist}
    (hD : D' = D)
    (hL : L' = L)
    (hU : U' = U)
    (hQ : Q' = Q)
    (hS : S' = S)
    (hR : R' = R)
    (hE : E' = E)
    (hO : O' = O)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    DedekindCutArithmeticUp.mk D' L' U' Q' S' R' E' O' H' C' P' N' =
      DedekindCutArithmeticUp.mk D L U Q S R E O H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hL
  cases hU
  cases hQ
  cases hS
  cases hR
  cases hE
  cases hO
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def dedekindCutArithmeticFields :
    DedekindCutArithmeticUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindCutArithmeticUp.mk D L U Q S R E O H C P N =>
      [D, L, U, Q, S, R, E, O, H, C, P, N]

def dedekindCutArithmeticToEventFlow :
    DedekindCutArithmeticUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | pkt =>
      (dedekindCutArithmeticFields pkt).map dedekindCutArithmeticEncodeBHist

def dedekindCutArithmeticFromEventFlow :
    EventFlow → Option DedekindCutArithmeticUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | L :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | O :: rest7 =>
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
                                                        (DedekindCutArithmeticUp.mk
                                                          (dedekindCutArithmeticDecodeBHist D)
                                                          (dedekindCutArithmeticDecodeBHist L)
                                                          (dedekindCutArithmeticDecodeBHist U)
                                                          (dedekindCutArithmeticDecodeBHist Q)
                                                          (dedekindCutArithmeticDecodeBHist S)
                                                          (dedekindCutArithmeticDecodeBHist R)
                                                          (dedekindCutArithmeticDecodeBHist E)
                                                          (dedekindCutArithmeticDecodeBHist O)
                                                          (dedekindCutArithmeticDecodeBHist H)
                                                          (dedekindCutArithmeticDecodeBHist C)
                                                          (dedekindCutArithmeticDecodeBHist P)
                                                          (dedekindCutArithmeticDecodeBHist N))
                                                  | _ :: _ => none

private theorem dedekindCutArithmetic_round_trip :
    ∀ pkt : DedekindCutArithmeticUp,
      dedekindCutArithmeticFromEventFlow
        (dedekindCutArithmeticToEventFlow pkt) = some pkt := by
  -- BEDC touchpoint anchor: BHist BMark
  intro pkt
  cases pkt with
  | mk D L U Q S R E O H C P N =>
      change
        some
          (DedekindCutArithmeticUp.mk
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist D))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist L))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist U))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist Q))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist S))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist R))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist E))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist O))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist H))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist C))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist P))
            (dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist N))) =
          some (DedekindCutArithmeticUp.mk D L U Q S R E O H C P N)
      exact
        congrArg some
          (dedekindCutArithmetic_mk_congr
            (dedekindCutArithmeticDecode_encode_bhist D)
            (dedekindCutArithmeticDecode_encode_bhist L)
            (dedekindCutArithmeticDecode_encode_bhist U)
            (dedekindCutArithmeticDecode_encode_bhist Q)
            (dedekindCutArithmeticDecode_encode_bhist S)
            (dedekindCutArithmeticDecode_encode_bhist R)
            (dedekindCutArithmeticDecode_encode_bhist E)
            (dedekindCutArithmeticDecode_encode_bhist O)
            (dedekindCutArithmeticDecode_encode_bhist H)
            (dedekindCutArithmeticDecode_encode_bhist C)
            (dedekindCutArithmeticDecode_encode_bhist P)
            (dedekindCutArithmeticDecode_encode_bhist N))

private theorem dedekindCutArithmeticToEventFlow_injective
    {x y : DedekindCutArithmeticUp} :
    dedekindCutArithmeticToEventFlow x =
      dedekindCutArithmeticToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindCutArithmeticFromEventFlow
          (dedekindCutArithmeticToEventFlow x) =
        dedekindCutArithmeticFromEventFlow
          (dedekindCutArithmeticToEventFlow y) :=
    congrArg dedekindCutArithmeticFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dedekindCutArithmetic_round_trip x).symm
      (Eq.trans hread (dedekindCutArithmetic_round_trip y)))

instance dedekindCutArithmeticBHistCarrier :
    BHistCarrier DedekindCutArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCutArithmeticToEventFlow
  fromEventFlow := dedekindCutArithmeticFromEventFlow

instance dedekindCutArithmeticChapterTasteGate :
    ChapterTasteGate DedekindCutArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindCutArithmeticFromEventFlow
        (dedekindCutArithmeticToEventFlow x) = some x
    exact dedekindCutArithmetic_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindCutArithmeticToEventFlow_injective heq)

theorem DedekindCutArithmeticTasteGate_single_carrier_alignment :
    (∀ h : BHist, dedekindCutArithmeticDecodeBHist (dedekindCutArithmeticEncodeBHist h) = h) ∧
      (∀ x : DedekindCutArithmeticUp,
        dedekindCutArithmeticFromEventFlow (dedekindCutArithmeticToEventFlow x) = some x) ∧
        (∀ x y : DedekindCutArithmeticUp,
          dedekindCutArithmeticToEventFlow x = dedekindCutArithmeticToEventFlow y -> x = y) ∧
          dedekindCutArithmeticEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dedekindCutArithmeticDecode_encode_bhist
  · constructor
    · exact dedekindCutArithmetic_round_trip
    · constructor
      · intro x y heq
        exact dedekindCutArithmeticToEventFlow_injective heq
      · rfl

end BEDC.Derived.DedekindCutArithmeticUp
