import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionUniquenessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCompletionUniquenessUp : Type where
  | mk :
      (uniformSource completionPresentations cauchyFilter separatedComparison metricComparison
        streamWindows readbackSeal componentTransport replay provenance localName : BHist) →
      UniformCompletionUniquenessUp
  deriving DecidableEq

def uniformCompletionUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompletionUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompletionUniquenessEncodeBHist h

def uniformCompletionUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompletionUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompletionUniquenessDecodeBHist tail)

private theorem uniformCompletionUniquenessDecode_encode_bhist :
    ∀ h : BHist,
      uniformCompletionUniquenessDecodeBHist
        (uniformCompletionUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCompletionUniquenessToEventFlow :
    UniformCompletionUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompletionUniquenessUp.mk uniformSource completionPresentations cauchyFilter
      separatedComparison metricComparison streamWindows readbackSeal componentTransport replay
      provenance localName =>
      [uniformCompletionUniquenessEncodeBHist uniformSource,
        uniformCompletionUniquenessEncodeBHist completionPresentations,
        uniformCompletionUniquenessEncodeBHist cauchyFilter,
        uniformCompletionUniquenessEncodeBHist separatedComparison,
        uniformCompletionUniquenessEncodeBHist metricComparison,
        uniformCompletionUniquenessEncodeBHist streamWindows,
        uniformCompletionUniquenessEncodeBHist readbackSeal,
        uniformCompletionUniquenessEncodeBHist componentTransport,
        uniformCompletionUniquenessEncodeBHist replay,
        uniformCompletionUniquenessEncodeBHist provenance,
        uniformCompletionUniquenessEncodeBHist localName]

def uniformCompletionUniquenessFromEventFlow :
    EventFlow → Option UniformCompletionUniquenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | uniformSource :: rest0 =>
      match rest0 with
      | [] => none
      | completionPresentations :: rest1 =>
          match rest1 with
          | [] => none
          | cauchyFilter :: rest2 =>
              match rest2 with
              | [] => none
              | separatedComparison :: rest3 =>
                  match rest3 with
                  | [] => none
                  | metricComparison :: rest4 =>
                      match rest4 with
                      | [] => none
                      | streamWindows :: rest5 =>
                          match rest5 with
                          | [] => none
                          | readbackSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | componentTransport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (UniformCompletionUniquenessUp.mk
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        uniformSource)
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        completionPresentations)
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        cauchyFilter)
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        separatedComparison)
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        metricComparison)
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        streamWindows)
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        readbackSeal)
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        componentTransport)
                                                      (uniformCompletionUniquenessDecodeBHist replay)
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        provenance)
                                                      (uniformCompletionUniquenessDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem uniformCompletionUniqueness_round_trip :
    ∀ x : UniformCompletionUniquenessUp,
      uniformCompletionUniquenessFromEventFlow
        (uniformCompletionUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk uniformSource completionPresentations cauchyFilter separatedComparison metricComparison
      streamWindows readbackSeal componentTransport replay provenance localName =>
      change
        some
          (UniformCompletionUniquenessUp.mk
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist uniformSource))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist completionPresentations))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist cauchyFilter))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist separatedComparison))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist metricComparison))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist streamWindows))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist readbackSeal))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist componentTransport))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist replay))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist provenance))
            (uniformCompletionUniquenessDecodeBHist
              (uniformCompletionUniquenessEncodeBHist localName))) =
          some
            (UniformCompletionUniquenessUp.mk uniformSource completionPresentations cauchyFilter
              separatedComparison metricComparison streamWindows readbackSeal componentTransport
              replay provenance localName)
      rw [uniformCompletionUniquenessDecode_encode_bhist uniformSource,
        uniformCompletionUniquenessDecode_encode_bhist completionPresentations,
        uniformCompletionUniquenessDecode_encode_bhist cauchyFilter,
        uniformCompletionUniquenessDecode_encode_bhist separatedComparison,
        uniformCompletionUniquenessDecode_encode_bhist metricComparison,
        uniformCompletionUniquenessDecode_encode_bhist streamWindows,
        uniformCompletionUniquenessDecode_encode_bhist readbackSeal,
        uniformCompletionUniquenessDecode_encode_bhist componentTransport,
        uniformCompletionUniquenessDecode_encode_bhist replay,
        uniformCompletionUniquenessDecode_encode_bhist provenance,
        uniformCompletionUniquenessDecode_encode_bhist localName]

private theorem uniformCompletionUniquenessToEventFlow_injective
    {x y : UniformCompletionUniquenessUp} :
    uniformCompletionUniquenessToEventFlow x =
      uniformCompletionUniquenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCompletionUniquenessFromEventFlow
          (uniformCompletionUniquenessToEventFlow x) =
        uniformCompletionUniquenessFromEventFlow
          (uniformCompletionUniquenessToEventFlow y) :=
    congrArg uniformCompletionUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCompletionUniqueness_round_trip x).symm
      (Eq.trans hread (uniformCompletionUniqueness_round_trip y)))

def uniformCompletionUniquenessCarrier :
    BHistCarrier UniformCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompletionUniquenessToEventFlow
  fromEventFlow := uniformCompletionUniquenessFromEventFlow

instance uniformCompletionUniquenessBHistCarrier :
    BHistCarrier UniformCompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCompletionUniquenessCarrier

def uniformCompletionUniquenessGate :
    @ChapterTasteGate UniformCompletionUniquenessUp uniformCompletionUniquenessCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCompletionUniquenessFromEventFlow
        (uniformCompletionUniquenessToEventFlow x) = some x
    exact uniformCompletionUniqueness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCompletionUniquenessToEventFlow_injective heq)

instance uniformCompletionUniquenessChapterTasteGate :
    ChapterTasteGate UniformCompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCompletionUniquenessGate

theorem UniformCompletionUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformCompletionUniquenessDecodeBHist (uniformCompletionUniquenessEncodeBHist h) = h) ∧
      (∀ x : UniformCompletionUniquenessUp,
        uniformCompletionUniquenessFromEventFlow
          (uniformCompletionUniquenessToEventFlow x) = some x) ∧
        (∀ x y : UniformCompletionUniquenessUp,
          uniformCompletionUniquenessToEventFlow x =
            uniformCompletionUniquenessToEventFlow y → x = y) ∧
          uniformCompletionUniquenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨uniformCompletionUniquenessDecode_encode_bhist,
      ⟨uniformCompletionUniqueness_round_trip,
        ⟨(fun _ _ heq => uniformCompletionUniquenessToEventFlow_injective heq), rfl⟩⟩⟩

end BEDC.Derived.UniformCompletionUniquenessUp.TasteGate
