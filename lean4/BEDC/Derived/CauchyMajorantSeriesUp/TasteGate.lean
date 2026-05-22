import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyMajorantSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyMajorantSeriesUp : Type where
  | mk (A D S R B E H C P N : BHist) : CauchyMajorantSeriesUp
  deriving DecidableEq

def cauchyMajorantSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyMajorantSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyMajorantSeriesEncodeBHist h

def cauchyMajorantSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyMajorantSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyMajorantSeriesDecodeBHist tail)

private theorem cauchyMajorantSeries_decode_encode_bhist :
    ∀ h : BHist,
      cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cauchyMajorantSeries_mk_congr
    {A A' D D' S S' R R' B B' E E' H H' C C' P P' N N' : BHist}
    (hA : A' = A) (hD : D' = D) (hS : S' = S) (hR : R' = R)
    (hB : B' = B) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyMajorantSeriesUp.mk A' D' S' R' B' E' H' C' P' N' =
      CauchyMajorantSeriesUp.mk A D S R B E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hD
  cases hS
  cases hR
  cases hB
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyMajorantSeriesFields : CauchyMajorantSeriesUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyMajorantSeriesUp.mk A D S R B E H C P N => [A, D, S, R, B, E, H, C, P, N]

def cauchyMajorantSeriesToEventFlow : CauchyMajorantSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyMajorantSeriesFields x).map cauchyMajorantSeriesEncodeBHist

def cauchyMajorantSeriesFromEventFlow : EventFlow → Option CauchyMajorantSeriesUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyMajorantSeriesUp.mk
                                                  (cauchyMajorantSeriesDecodeBHist A)
                                                  (cauchyMajorantSeriesDecodeBHist D)
                                                  (cauchyMajorantSeriesDecodeBHist S)
                                                  (cauchyMajorantSeriesDecodeBHist R)
                                                  (cauchyMajorantSeriesDecodeBHist B)
                                                  (cauchyMajorantSeriesDecodeBHist E)
                                                  (cauchyMajorantSeriesDecodeBHist H)
                                                  (cauchyMajorantSeriesDecodeBHist C)
                                                  (cauchyMajorantSeriesDecodeBHist P)
                                                  (cauchyMajorantSeriesDecodeBHist N))
                                          | _ :: _ => none

private theorem cauchyMajorantSeries_round_trip :
    ∀ x : CauchyMajorantSeriesUp,
      cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A D S R B E H C P N =>
      exact
        congrArg some
          (cauchyMajorantSeries_mk_congr
            (cauchyMajorantSeries_decode_encode_bhist A)
            (cauchyMajorantSeries_decode_encode_bhist D)
            (cauchyMajorantSeries_decode_encode_bhist S)
            (cauchyMajorantSeries_decode_encode_bhist R)
            (cauchyMajorantSeries_decode_encode_bhist B)
            (cauchyMajorantSeries_decode_encode_bhist E)
            (cauchyMajorantSeries_decode_encode_bhist H)
            (cauchyMajorantSeries_decode_encode_bhist C)
            (cauchyMajorantSeries_decode_encode_bhist P)
            (cauchyMajorantSeries_decode_encode_bhist N))

private theorem cauchyMajorantSeriesToEventFlow_injective {x y : CauchyMajorantSeriesUp} :
    cauchyMajorantSeriesToEventFlow x = cauchyMajorantSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) =
        cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow y) :=
    congrArg cauchyMajorantSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyMajorantSeries_round_trip x).symm
      (Eq.trans hread (cauchyMajorantSeries_round_trip y)))

instance cauchyMajorantSeriesBHistCarrier : BHistCarrier CauchyMajorantSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyMajorantSeriesToEventFlow
  fromEventFlow := cauchyMajorantSeriesFromEventFlow

instance cauchyMajorantSeriesChapterTasteGate : ChapterTasteGate CauchyMajorantSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) = some x
    exact cauchyMajorantSeries_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyMajorantSeriesToEventFlow_injective heq)

namespace TasteGate

theorem CauchyMajorantSeriesTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist h) = h) ∧
      (∀ x : CauchyMajorantSeriesUp,
        cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) = some x) ∧
        (∀ x y : CauchyMajorantSeriesUp,
          cauchyMajorantSeriesToEventFlow x = cauchyMajorantSeriesToEventFlow y → x = y) ∧
          cauchyMajorantSeriesEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact cauchyMajorantSeries_decode_encode_bhist
  · constructor
    · exact cauchyMajorantSeries_round_trip
    · constructor
      · intro x y heq
        exact cauchyMajorantSeriesToEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.CauchyMajorantSeriesUp
