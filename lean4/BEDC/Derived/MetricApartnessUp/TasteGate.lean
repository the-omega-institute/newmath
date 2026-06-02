import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricApartnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricApartnessUp : Type where
  | mk (M x y D R Z S Q H C P N : BHist) : MetricApartnessUp
  deriving DecidableEq

def metricApartnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricApartnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricApartnessEncodeBHist h

def metricApartnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricApartnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricApartnessDecodeBHist tail)

private theorem metricApartnessDecode_encode_bhist :
    ∀ h : BHist, metricApartnessDecodeBHist (metricApartnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricApartnessFields : MetricApartnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricApartnessUp.mk M x y D R Z S Q H C P N => [M, x, y, D, R, Z, S, Q, H, C, P, N]

def metricApartnessToEventFlow : MetricApartnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricApartnessFields x).map metricApartnessEncodeBHist

def metricApartnessFromEventFlow : EventFlow → Option MetricApartnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | x :: rest1 =>
          match rest1 with
          | [] => none
          | y :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Z :: rest5 =>
                          match rest5 with
                          | [] => none
                          | S :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Q :: rest7 =>
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
                                                        (MetricApartnessUp.mk
                                                          (metricApartnessDecodeBHist M)
                                                          (metricApartnessDecodeBHist x)
                                                          (metricApartnessDecodeBHist y)
                                                          (metricApartnessDecodeBHist D)
                                                          (metricApartnessDecodeBHist R)
                                                          (metricApartnessDecodeBHist Z)
                                                          (metricApartnessDecodeBHist S)
                                                          (metricApartnessDecodeBHist Q)
                                                          (metricApartnessDecodeBHist H)
                                                          (metricApartnessDecodeBHist C)
                                                          (metricApartnessDecodeBHist P)
                                                          (metricApartnessDecodeBHist N))
                                                  | _ :: _ => none

private theorem metricApartness_round_trip :
    ∀ x : MetricApartnessUp, metricApartnessFromEventFlow (metricApartnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M x y D R Z S Q H C P N =>
      change
        some
          (MetricApartnessUp.mk
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist M))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist x))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist y))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist D))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist R))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist Z))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist S))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist Q))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist H))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist C))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist P))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist N))) =
          some (MetricApartnessUp.mk M x y D R Z S Q H C P N)
      rw [metricApartnessDecode_encode_bhist M, metricApartnessDecode_encode_bhist x,
        metricApartnessDecode_encode_bhist y, metricApartnessDecode_encode_bhist D,
        metricApartnessDecode_encode_bhist R, metricApartnessDecode_encode_bhist Z,
        metricApartnessDecode_encode_bhist S, metricApartnessDecode_encode_bhist Q,
        metricApartnessDecode_encode_bhist H, metricApartnessDecode_encode_bhist C,
        metricApartnessDecode_encode_bhist P, metricApartnessDecode_encode_bhist N]

private theorem metricApartnessToEventFlow_injective {x y : MetricApartnessUp} :
    metricApartnessToEventFlow x = metricApartnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricApartnessFromEventFlow (metricApartnessToEventFlow x) =
        metricApartnessFromEventFlow (metricApartnessToEventFlow y) :=
    congrArg metricApartnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricApartness_round_trip x).symm (Eq.trans hread (metricApartness_round_trip y)))

instance metricApartnessBHistCarrier : BHistCarrier MetricApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricApartnessToEventFlow
  fromEventFlow := metricApartnessFromEventFlow

instance metricApartnessChapterTasteGate : ChapterTasteGate MetricApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricApartnessFromEventFlow (metricApartnessToEventFlow x) = some x
    exact metricApartness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricApartnessToEventFlow_injective heq)

theorem MetricApartnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricApartnessDecodeBHist (metricApartnessEncodeBHist h) = h) ∧
      (∀ x : MetricApartnessUp, metricApartnessFromEventFlow (metricApartnessToEventFlow x) = some x) ∧
        (∀ x y : MetricApartnessUp, metricApartnessToEventFlow x = metricApartnessToEventFlow y → x = y) ∧
          metricApartnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨metricApartnessDecode_encode_bhist, metricApartness_round_trip,
      fun _ _ heq => metricApartnessToEventFlow_injective heq, rfl⟩

end BEDC.Derived.MetricApartnessUp.TasteGate
