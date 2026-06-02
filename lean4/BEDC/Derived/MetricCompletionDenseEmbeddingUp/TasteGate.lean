import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionDenseEmbeddingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionDenseEmbeddingUp : Type where
  | mk (X C E S U R H K P N : BHist) : MetricCompletionDenseEmbeddingUp
  deriving DecidableEq

def metricCompletionDenseEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionDenseEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionDenseEmbeddingEncodeBHist h

def metricCompletionDenseEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionDenseEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionDenseEmbeddingDecodeBHist tail)

private theorem metricCompletionDenseEmbeddingDecodeEncode :
    forall h : BHist,
      metricCompletionDenseEmbeddingDecodeBHist
          (metricCompletionDenseEmbeddingEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem metricCompletionDenseEmbeddingMkCongr
    {X X' C C' E E' S S' U U' R R' H H' K K' P P' N N' : BHist}
    (hX : X' = X)
    (hC : C' = C)
    (hE : E' = E)
    (hS : S' = S)
    (hU : U' = U)
    (hR : R' = R)
    (hH : H' = H)
    (hK : K' = K)
    (hP : P' = P)
    (hN : N' = N) :
    MetricCompletionDenseEmbeddingUp.mk X' C' E' S' U' R' H' K' P' N' =
      MetricCompletionDenseEmbeddingUp.mk X C E S U R H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hC
  cases hE
  cases hS
  cases hU
  cases hR
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

def metricCompletionDenseEmbeddingFields :
    MetricCompletionDenseEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionDenseEmbeddingUp.mk X C E S U R H K P N => [X, C, E, S, U, R, H, K, P, N]

def metricCompletionDenseEmbeddingToEventFlow : MetricCompletionDenseEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionDenseEmbeddingUp.mk X C E S U R H K P N =>
      [[BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist X,
        [BMark.b1, BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metricCompletionDenseEmbeddingEncodeBHist N]

def metricCompletionDenseEmbeddingFromEventFlow :
    EventFlow → Option MetricCompletionDenseEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | X :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | C :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | S :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | U :: rest9 =>
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
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | K :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MetricCompletionDenseEmbeddingUp.mk
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            X)
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            C)
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            E)
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            S)
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            U)
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            R)
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            H)
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            K)
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            P)
                                                                                          (metricCompletionDenseEmbeddingDecodeBHist
                                                                                            N))
                                                                                  | _ :: _ => none

private theorem metricCompletionDenseEmbeddingRoundTrip :
    forall x : MetricCompletionDenseEmbeddingUp,
      metricCompletionDenseEmbeddingFromEventFlow
          (metricCompletionDenseEmbeddingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X C E S U R H K P N =>
      change
        some
            (MetricCompletionDenseEmbeddingUp.mk
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist X))
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist C))
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist E))
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist S))
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist U))
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist R))
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist H))
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist K))
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist P))
              (metricCompletionDenseEmbeddingDecodeBHist
                (metricCompletionDenseEmbeddingEncodeBHist N))) =
          some (MetricCompletionDenseEmbeddingUp.mk X C E S U R H K P N)
      exact
        congrArg some
          (metricCompletionDenseEmbeddingMkCongr
            (metricCompletionDenseEmbeddingDecodeEncode X)
            (metricCompletionDenseEmbeddingDecodeEncode C)
            (metricCompletionDenseEmbeddingDecodeEncode E)
            (metricCompletionDenseEmbeddingDecodeEncode S)
            (metricCompletionDenseEmbeddingDecodeEncode U)
            (metricCompletionDenseEmbeddingDecodeEncode R)
            (metricCompletionDenseEmbeddingDecodeEncode H)
            (metricCompletionDenseEmbeddingDecodeEncode K)
            (metricCompletionDenseEmbeddingDecodeEncode P)
            (metricCompletionDenseEmbeddingDecodeEncode N))

private theorem metricCompletionDenseEmbeddingToEventFlow_injective
    {x y : MetricCompletionDenseEmbeddingUp} :
    metricCompletionDenseEmbeddingToEventFlow x =
        metricCompletionDenseEmbeddingToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          metricCompletionDenseEmbeddingFromEventFlow
            (metricCompletionDenseEmbeddingToEventFlow x) :=
        (metricCompletionDenseEmbeddingRoundTrip x).symm
      _ =
          metricCompletionDenseEmbeddingFromEventFlow
            (metricCompletionDenseEmbeddingToEventFlow y) :=
        congrArg metricCompletionDenseEmbeddingFromEventFlow hxy
      _ = some y := metricCompletionDenseEmbeddingRoundTrip y
  exact Option.some.inj optionEq

instance metricCompletionDenseEmbeddingBHistCarrier :
    BHistCarrier MetricCompletionDenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionDenseEmbeddingToEventFlow
  fromEventFlow := metricCompletionDenseEmbeddingFromEventFlow

instance metricCompletionDenseEmbeddingChapterTasteGate :
    ChapterTasteGate MetricCompletionDenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionDenseEmbeddingFromEventFlow
          (metricCompletionDenseEmbeddingToEventFlow x) =
        some x
    exact metricCompletionDenseEmbeddingRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricCompletionDenseEmbeddingToEventFlow_injective heq)

theorem MetricCompletionDenseEmbeddingTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metricCompletionDenseEmbeddingDecodeBHist
          (metricCompletionDenseEmbeddingEncodeBHist h) =
        h) ∧
      (forall x : MetricCompletionDenseEmbeddingUp,
        metricCompletionDenseEmbeddingFromEventFlow
            (metricCompletionDenseEmbeddingToEventFlow x) =
          some x) ∧
        metricCompletionDenseEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨metricCompletionDenseEmbeddingDecodeEncode,
    metricCompletionDenseEmbeddingRoundTrip, rfl⟩

end BEDC.Derived.MetricCompletionDenseEmbeddingUp.TasteGate
