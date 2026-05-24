import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteSeparatedMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteSeparatedMetricUp : Type where
  | mk (X C S E R H K P N : BHist) : CompleteSeparatedMetricUp
  deriving DecidableEq

def completeSeparatedMetricEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeSeparatedMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeSeparatedMetricEncodeBHist h

def completeSeparatedMetricDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeSeparatedMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeSeparatedMetricDecodeBHist tail)

private theorem completeSeparatedMetric_decode_encode_bhist :
    forall h : BHist,
      completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem CompleteSeparatedMetricTasteGate_single_carrier_alignment_encode_injective
    {h k : BHist} :
    completeSeparatedMetricEncodeBHist h = completeSeparatedMetricEncodeBHist k -> h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist h) =
        completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist k) :=
    congrArg completeSeparatedMetricDecodeBHist heq
  exact
    Eq.trans (completeSeparatedMetric_decode_encode_bhist h).symm
      (Eq.trans hread (completeSeparatedMetric_decode_encode_bhist k))

private theorem CompleteSeparatedMetricTasteGate_single_carrier_alignment_mk_congr
    {X1 X2 C1 C2 S1 S2 E1 E2 R1 R2 H1 H2 K1 K2 P1 P2 N1 N2 : BHist}
    (hX : X1 = X2) (hC : C1 = C2) (hS : S1 = S2) (hE : E1 = E2)
    (hR : R1 = R2) (hH : H1 = H2) (hK : K1 = K2) (hP : P1 = P2)
    (hN : N1 = N2) :
    CompleteSeparatedMetricUp.mk X1 C1 S1 E1 R1 H1 K1 P1 N1 =
      CompleteSeparatedMetricUp.mk X2 C2 S2 E2 R2 H2 K2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hC
  cases hS
  cases hE
  cases hR
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

def completeSeparatedMetricFields : CompleteSeparatedMetricUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteSeparatedMetricUp.mk X C S E R H K P N => [X, C, S, E, R, H, K, P, N]

def completeSeparatedMetricToEventFlow : CompleteSeparatedMetricUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map completeSeparatedMetricEncodeBHist (completeSeparatedMetricFields x)

def completeSeparatedMetricFromEventFlow : EventFlow -> Option CompleteSeparatedMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | C :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | K :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CompleteSeparatedMetricUp.mk
                                              (completeSeparatedMetricDecodeBHist X)
                                              (completeSeparatedMetricDecodeBHist C)
                                              (completeSeparatedMetricDecodeBHist S)
                                              (completeSeparatedMetricDecodeBHist E)
                                              (completeSeparatedMetricDecodeBHist R)
                                              (completeSeparatedMetricDecodeBHist H)
                                              (completeSeparatedMetricDecodeBHist K)
                                              (completeSeparatedMetricDecodeBHist P)
                                              (completeSeparatedMetricDecodeBHist N))
                                      | _ :: _ => none

private theorem completeSeparatedMetric_round_trip :
    forall x : CompleteSeparatedMetricUp,
      completeSeparatedMetricFromEventFlow (completeSeparatedMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X C S E R H K P N =>
      change
        some
          (CompleteSeparatedMetricUp.mk
            (completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist X))
            (completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist C))
            (completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist S))
            (completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist E))
            (completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist R))
            (completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist H))
            (completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist K))
            (completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist P))
            (completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist N))) =
          some (CompleteSeparatedMetricUp.mk X C S E R H K P N)
      exact
        congrArg some
          (CompleteSeparatedMetricTasteGate_single_carrier_alignment_mk_congr
            (completeSeparatedMetric_decode_encode_bhist X)
            (completeSeparatedMetric_decode_encode_bhist C)
            (completeSeparatedMetric_decode_encode_bhist S)
            (completeSeparatedMetric_decode_encode_bhist E)
            (completeSeparatedMetric_decode_encode_bhist R)
            (completeSeparatedMetric_decode_encode_bhist H)
            (completeSeparatedMetric_decode_encode_bhist K)
            (completeSeparatedMetric_decode_encode_bhist P)
            (completeSeparatedMetric_decode_encode_bhist N))

private theorem CompleteSeparatedMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompleteSeparatedMetricUp} :
    completeSeparatedMetricToEventFlow x = completeSeparatedMetricToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeSeparatedMetricFromEventFlow (completeSeparatedMetricToEventFlow x) =
        completeSeparatedMetricFromEventFlow (completeSeparatedMetricToEventFlow y) :=
    congrArg completeSeparatedMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeSeparatedMetric_round_trip x).symm
      (Eq.trans hread (completeSeparatedMetric_round_trip y)))

instance completeSeparatedMetricBHistCarrier : BHistCarrier CompleteSeparatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeSeparatedMetricToEventFlow
  fromEventFlow := completeSeparatedMetricFromEventFlow

instance completeSeparatedMetricChapterTasteGate : ChapterTasteGate CompleteSeparatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeSeparatedMetricFromEventFlow (completeSeparatedMetricToEventFlow x) = some x
    exact completeSeparatedMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompleteSeparatedMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompleteSeparatedMetricTasteGate_single_carrier_alignment :
    (forall h : BHist,
      completeSeparatedMetricDecodeBHist (completeSeparatedMetricEncodeBHist h) = h) ∧
      (forall x : CompleteSeparatedMetricUp,
        completeSeparatedMetricFromEventFlow (completeSeparatedMetricToEventFlow x) = some x) ∧
        (forall x y : CompleteSeparatedMetricUp,
          completeSeparatedMetricToEventFlow x = completeSeparatedMetricToEventFlow y -> x = y) ∧
          completeSeparatedMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact completeSeparatedMetric_decode_encode_bhist
  · constructor
    · exact completeSeparatedMetric_round_trip
    · constructor
      · exact fun _x _y heq =>
          CompleteSeparatedMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CompleteSeparatedMetricUp
