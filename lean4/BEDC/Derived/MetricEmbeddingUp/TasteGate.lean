import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricEmbeddingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricEmbeddingUp : Type where
  | mk (X Y F D R S H C P N : BHist) : MetricEmbeddingUp
  deriving DecidableEq

def metricEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricEmbeddingEncodeBHist h

def metricEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricEmbeddingDecodeBHist tail)

private theorem metricEmbedding_decode_encode :
    ∀ h : BHist, metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricEmbeddingFields : MetricEmbeddingUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MetricEmbeddingUp.mk X Y F D R S H C P N => [X, Y, F, D, R, S, H, C, P, N]

def metricEmbeddingToEventFlow : MetricEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MetricEmbeddingUp.mk X Y F D R S H C P N =>
      [metricEmbeddingEncodeBHist X,
        metricEmbeddingEncodeBHist Y,
        metricEmbeddingEncodeBHist F,
        metricEmbeddingEncodeBHist D,
        metricEmbeddingEncodeBHist R,
        metricEmbeddingEncodeBHist S,
        metricEmbeddingEncodeBHist H,
        metricEmbeddingEncodeBHist C,
        metricEmbeddingEncodeBHist P,
        metricEmbeddingEncodeBHist N]

def metricEmbeddingFromEventFlow : EventFlow → Option MetricEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => none
  | _X :: [] => none
  | _X :: _Y :: [] => none
  | _X :: _Y :: _F :: [] => none
  | _X :: _Y :: _F :: _D :: [] => none
  | _X :: _Y :: _F :: _D :: _R :: [] => none
  | _X :: _Y :: _F :: _D :: _R :: _S :: [] => none
  | _X :: _Y :: _F :: _D :: _R :: _S :: _H :: [] => none
  | _X :: _Y :: _F :: _D :: _R :: _S :: _H :: _C :: [] => none
  | _X :: _Y :: _F :: _D :: _R :: _S :: _H :: _C :: _P :: [] => none
  | X :: Y :: F :: D :: R :: S :: H :: C :: P :: N :: [] =>
      some
        (MetricEmbeddingUp.mk
          (metricEmbeddingDecodeBHist X)
          (metricEmbeddingDecodeBHist Y)
          (metricEmbeddingDecodeBHist F)
          (metricEmbeddingDecodeBHist D)
          (metricEmbeddingDecodeBHist R)
          (metricEmbeddingDecodeBHist S)
          (metricEmbeddingDecodeBHist H)
          (metricEmbeddingDecodeBHist C)
          (metricEmbeddingDecodeBHist P)
          (metricEmbeddingDecodeBHist N))
  | _X :: _Y :: _F :: _D :: _R :: _S :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

private theorem metricEmbedding_round_trip :
    ∀ x : MetricEmbeddingUp,
      metricEmbeddingFromEventFlow (metricEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y F D R S H C P N =>
      exact
        Eq.trans
          (congrArg
            (fun z =>
              some
                (MetricEmbeddingUp.mk z
                  (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist Y))
                  (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist F))
                  (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist D))
                  (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist R))
                  (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist S))
                  (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist H))
                  (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist C))
                  (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist P))
                  (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist N))))
            (metricEmbedding_decode_encode X))
          (Eq.trans
            (congrArg
              (fun z =>
                some
                  (MetricEmbeddingUp.mk X z
                    (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist F))
                    (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist D))
                    (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist R))
                    (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist S))
                    (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist H))
                    (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist C))
                    (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist P))
                    (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist N))))
              (metricEmbedding_decode_encode Y))
            (Eq.trans
              (congrArg
                (fun z =>
                  some
                    (MetricEmbeddingUp.mk X Y z
                      (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist D))
                      (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist R))
                      (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist S))
                      (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist H))
                      (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist C))
                      (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist P))
                      (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist N))))
                (metricEmbedding_decode_encode F))
              (Eq.trans
                (congrArg
                  (fun z =>
                    some
                      (MetricEmbeddingUp.mk X Y F z
                        (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist R))
                        (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist S))
                        (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist H))
                        (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist C))
                        (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist P))
                        (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist N))))
                  (metricEmbedding_decode_encode D))
                (Eq.trans
                  (congrArg
                    (fun z =>
                      some
                        (MetricEmbeddingUp.mk X Y F D z
                          (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist S))
                          (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist H))
                          (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist C))
                          (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist P))
                          (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist N))))
                    (metricEmbedding_decode_encode R))
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        some
                          (MetricEmbeddingUp.mk X Y F D R z
                            (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist H))
                            (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist C))
                            (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist P))
                            (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist N))))
                      (metricEmbedding_decode_encode S))
                    (Eq.trans
                      (congrArg
                        (fun z =>
                          some
                            (MetricEmbeddingUp.mk X Y F D R S z
                              (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist C))
                              (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist P))
                              (metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist N))))
                        (metricEmbedding_decode_encode H))
                      (Eq.trans
                        (congrArg
                          (fun z =>
                            some
                              (MetricEmbeddingUp.mk X Y F D R S H z
                                (metricEmbeddingDecodeBHist
                                  (metricEmbeddingEncodeBHist P))
                                (metricEmbeddingDecodeBHist
                                  (metricEmbeddingEncodeBHist N))))
                          (metricEmbedding_decode_encode C))
                        (Eq.trans
                          (congrArg
                            (fun z =>
                              some
                                (MetricEmbeddingUp.mk X Y F D R S H C z
                                  (metricEmbeddingDecodeBHist
                                    (metricEmbeddingEncodeBHist N))))
                            (metricEmbedding_decode_encode P))
                          (congrArg
                            (fun z => some (MetricEmbeddingUp.mk X Y F D R S H C P z))
                            (metricEmbedding_decode_encode N))))))))))

private theorem metricEmbeddingToEventFlow_injective {x y : MetricEmbeddingUp} :
    metricEmbeddingToEventFlow x = metricEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      metricEmbeddingFromEventFlow (metricEmbeddingToEventFlow x) =
        metricEmbeddingFromEventFlow (metricEmbeddingToEventFlow y) :=
    congrArg metricEmbeddingFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (metricEmbedding_round_trip x).symm
      (Eq.trans hread (metricEmbedding_round_trip y)))

instance metricEmbeddingBHistCarrier : BHistCarrier MetricEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricEmbeddingToEventFlow
  fromEventFlow := metricEmbeddingFromEventFlow

instance metricEmbeddingChapterTasteGate : ChapterTasteGate MetricEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricEmbeddingFromEventFlow (metricEmbeddingToEventFlow x) = some x
    exact metricEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricEmbeddingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetricEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricEmbeddingChapterTasteGate

theorem MetricEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricEmbeddingDecodeBHist (metricEmbeddingEncodeBHist h) = h) ∧
      (∀ x : MetricEmbeddingUp,
        metricEmbeddingFromEventFlow (metricEmbeddingToEventFlow x) = some x) ∧
      (∀ x y : MetricEmbeddingUp,
        metricEmbeddingToEventFlow x = metricEmbeddingToEventFlow y → x = y) ∧
      metricEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact metricEmbedding_decode_encode h
  · constructor
    · intro x
      exact metricEmbedding_round_trip x
    · constructor
      · intro x y hxy
        have hread :
            metricEmbeddingFromEventFlow (metricEmbeddingToEventFlow x) =
              metricEmbeddingFromEventFlow (metricEmbeddingToEventFlow y) :=
          congrArg metricEmbeddingFromEventFlow hxy
        have hsome : some x = some y :=
          Eq.trans (metricEmbedding_round_trip x).symm
            (Eq.trans hread (metricEmbedding_round_trip y))
        exact Option.some.inj hsome
      · rfl

end BEDC.Derived.MetricEmbeddingUp.TasteGate
