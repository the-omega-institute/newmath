import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ComputableCompactMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ComputableCompactMetricUp : Type where
  | mk (K E T C S R L H Q P N : BHist) : ComputableCompactMetricUp
  deriving DecidableEq

def computableCompactMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: computableCompactMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: computableCompactMetricEncodeBHist h

def computableCompactMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (computableCompactMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (computableCompactMetricDecodeBHist tail)

private theorem computableCompactMetric_decode_encode :
    ∀ h : BHist, computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def computableCompactMetricFields : ComputableCompactMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ComputableCompactMetricUp.mk K E T C S R L H Q P N => [K, E, T, C, S, R, L, H, Q, P, N]

def computableCompactMetricToEventFlow : ComputableCompactMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (computableCompactMetricFields x).map computableCompactMetricEncodeBHist

def computableCompactMetricFromEventFlow : EventFlow → Option ComputableCompactMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | K :: restK =>
      match restK with
      | E :: restE =>
          match restE with
          | T :: restT =>
              match restT with
              | C :: restC =>
                  match restC with
                  | S :: restS =>
                      match restS with
                      | R :: restR =>
                          match restR with
                          | L :: restL =>
                              match restL with
                              | H :: restH =>
                                  match restH with
                                  | Q :: restQ =>
                                      match restQ with
                                      | P :: restP =>
                                          match restP with
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (ComputableCompactMetricUp.mk
                                                      (computableCompactMetricDecodeBHist K)
                                                      (computableCompactMetricDecodeBHist E)
                                                      (computableCompactMetricDecodeBHist T)
                                                      (computableCompactMetricDecodeBHist C)
                                                      (computableCompactMetricDecodeBHist S)
                                                      (computableCompactMetricDecodeBHist R)
                                                      (computableCompactMetricDecodeBHist L)
                                                      (computableCompactMetricDecodeBHist H)
                                                      (computableCompactMetricDecodeBHist Q)
                                                      (computableCompactMetricDecodeBHist P)
                                                      (computableCompactMetricDecodeBHist N))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem computableCompactMetric_round_trip :
    ∀ x : ComputableCompactMetricUp,
      computableCompactMetricFromEventFlow (computableCompactMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K E T C S R L H Q P N =>
      change
        some
            (ComputableCompactMetricUp.mk
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist K))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist E))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist T))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist C))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist S))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist R))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist L))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist H))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist Q))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist P))
              (computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist N))) =
          some (ComputableCompactMetricUp.mk K E T C S R L H Q P N)
      rw [computableCompactMetric_decode_encode K]
      rw [computableCompactMetric_decode_encode E]
      rw [computableCompactMetric_decode_encode T]
      rw [computableCompactMetric_decode_encode C]
      rw [computableCompactMetric_decode_encode S]
      rw [computableCompactMetric_decode_encode R]
      rw [computableCompactMetric_decode_encode L]
      rw [computableCompactMetric_decode_encode H]
      rw [computableCompactMetric_decode_encode Q]
      rw [computableCompactMetric_decode_encode P]
      rw [computableCompactMetric_decode_encode N]

private theorem computableCompactMetricToEventFlow_injective {x y : ComputableCompactMetricUp} :
    computableCompactMetricToEventFlow x = computableCompactMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      computableCompactMetricFromEventFlow (computableCompactMetricToEventFlow x) =
        computableCompactMetricFromEventFlow (computableCompactMetricToEventFlow y) :=
    congrArg computableCompactMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (computableCompactMetric_round_trip x).symm
      (Eq.trans hread (computableCompactMetric_round_trip y)))

instance computableCompactMetricBHistCarrier : BHistCarrier ComputableCompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := computableCompactMetricToEventFlow
  fromEventFlow := computableCompactMetricFromEventFlow

instance computableCompactMetricChapterTasteGate :
    ChapterTasteGate ComputableCompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change computableCompactMetricFromEventFlow (computableCompactMetricToEventFlow x) = some x
    exact computableCompactMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (computableCompactMetricToEventFlow_injective heq)

theorem ComputableCompactMetricTasteGate_single_carrier_alignment :
    (forall h : BHist,
      computableCompactMetricDecodeBHist (computableCompactMetricEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ComputableCompactMetricUp) ∧
      Nonempty (ChapterTasteGate ComputableCompactMetricUp) ∧
      computableCompactMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact computableCompactMetric_decode_encode
  · constructor
    · exact ⟨computableCompactMetricBHistCarrier⟩
    · constructor
      · exact ⟨computableCompactMetricChapterTasteGate⟩
      · rfl

end BEDC.Derived.ComputableCompactMetricUp
