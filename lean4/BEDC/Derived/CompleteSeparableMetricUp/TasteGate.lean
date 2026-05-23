import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteSeparableMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteSeparableMetricUp : Type where
  | mk (M K D W T R E H C P N : BHist) : CompleteSeparableMetricUp
  deriving DecidableEq

def completeSeparableMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeSeparableMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeSeparableMetricEncodeBHist h

def completeSeparableMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeSeparableMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeSeparableMetricDecodeBHist tail)

private theorem completeSeparableMetricDecode_encode_bhist :
    ∀ h : BHist, completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem completeSeparableMetric_mk_congr
    {M M' K K' D D' W W' T T' R R' E E' H H' C C' P P' N N' : BHist}
    (hM : M' = M)
    (hK : K' = K)
    (hD : D' = D)
    (hW : W' = W)
    (hT : T' = T)
    (hR : R' = R)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    CompleteSeparableMetricUp.mk M' K' D' W' T' R' E' H' C' P' N' =
      CompleteSeparableMetricUp.mk M K D W T R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hK
  cases hD
  cases hW
  cases hT
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def completeSeparableMetricToEventFlow : CompleteSeparableMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteSeparableMetricUp.mk M K D W T R E H C P N =>
      [[BMark.b0, BMark.b0],
        completeSeparableMetricEncodeBHist M,
        [BMark.b0, BMark.b1],
        completeSeparableMetricEncodeBHist K,
        [BMark.b1, BMark.b0],
        completeSeparableMetricEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        completeSeparableMetricEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        completeSeparableMetricEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        completeSeparableMetricEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        completeSeparableMetricEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        completeSeparableMetricEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        completeSeparableMetricEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        completeSeparableMetricEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        completeSeparableMetricEncodeBHist N]

def completeSeparableMetricFromEventFlow :
    EventFlow → Option CompleteSeparableMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | K :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | W :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | T :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | E :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CompleteSeparableMetricUp.mk
                                                                                                  (completeSeparableMetricDecodeBHist M)
                                                                                                  (completeSeparableMetricDecodeBHist K)
                                                                                                  (completeSeparableMetricDecodeBHist D)
                                                                                                  (completeSeparableMetricDecodeBHist W)
                                                                                                  (completeSeparableMetricDecodeBHist T)
                                                                                                  (completeSeparableMetricDecodeBHist R)
                                                                                                  (completeSeparableMetricDecodeBHist E)
                                                                                                  (completeSeparableMetricDecodeBHist H)
                                                                                                  (completeSeparableMetricDecodeBHist C)
                                                                                                  (completeSeparableMetricDecodeBHist P)
                                                                                                  (completeSeparableMetricDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem completeSeparableMetric_round_trip :
    ∀ x : CompleteSeparableMetricUp,
      completeSeparableMetricFromEventFlow
        (completeSeparableMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K D W T R E H C P N =>
      change
        some
          (CompleteSeparableMetricUp.mk
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist M))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist K))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist D))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist W))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist T))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist R))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist E))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist H))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist C))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist P))
            (completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist N))) =
          some (CompleteSeparableMetricUp.mk M K D W T R E H C P N)
      exact
        congrArg some
          (completeSeparableMetric_mk_congr
            (completeSeparableMetricDecode_encode_bhist M)
            (completeSeparableMetricDecode_encode_bhist K)
            (completeSeparableMetricDecode_encode_bhist D)
            (completeSeparableMetricDecode_encode_bhist W)
            (completeSeparableMetricDecode_encode_bhist T)
            (completeSeparableMetricDecode_encode_bhist R)
            (completeSeparableMetricDecode_encode_bhist E)
            (completeSeparableMetricDecode_encode_bhist H)
            (completeSeparableMetricDecode_encode_bhist C)
            (completeSeparableMetricDecode_encode_bhist P)
            (completeSeparableMetricDecode_encode_bhist N))

private theorem completeSeparableMetricToEventFlow_injective
    {x y : CompleteSeparableMetricUp} :
    completeSeparableMetricToEventFlow x =
      completeSeparableMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeSeparableMetricFromEventFlow
          (completeSeparableMetricToEventFlow x) =
        completeSeparableMetricFromEventFlow
          (completeSeparableMetricToEventFlow y) :=
    congrArg completeSeparableMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeSeparableMetric_round_trip x).symm
      (Eq.trans hread (completeSeparableMetric_round_trip y)))

instance completeSeparableMetricBHistCarrier :
    BHistCarrier CompleteSeparableMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeSeparableMetricToEventFlow
  fromEventFlow := completeSeparableMetricFromEventFlow

instance completeSeparableMetricChapterTasteGate :
    ChapterTasteGate CompleteSeparableMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      completeSeparableMetricFromEventFlow
        (completeSeparableMetricToEventFlow x) = some x
    exact completeSeparableMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completeSeparableMetricToEventFlow_injective heq)

theorem CompleteSeparableMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, completeSeparableMetricDecodeBHist (completeSeparableMetricEncodeBHist h) = h) ∧
      (∀ x : CompleteSeparableMetricUp,
        completeSeparableMetricFromEventFlow (completeSeparableMetricToEventFlow x) = some x) ∧
        (∀ x y : CompleteSeparableMetricUp,
          completeSeparableMetricToEventFlow x = completeSeparableMetricToEventFlow y → x = y) ∧
          completeSeparableMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact completeSeparableMetricDecode_encode_bhist
  · constructor
    · exact completeSeparableMetric_round_trip
    · constructor
      · intro x y heq
        exact completeSeparableMetricToEventFlow_injective heq
      · rfl

end BEDC.Derived.CompleteSeparableMetricUp
