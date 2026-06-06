import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocallyCompactMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocallyCompactMetricUp : Type where
  | mk
      (metric point neighbourhood compactWitness totallyBounded completeMetric radius transport
        replay provenance name : BHist) :
      LocallyCompactMetricUp

private def locallyCompactMetricEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locallyCompactMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locallyCompactMetricEncodeBHist h

private def locallyCompactMetricDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locallyCompactMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locallyCompactMetricDecodeBHist tail)

private theorem locallyCompactMetric_decode_encode_bhist :
    ∀ h : BHist,
      locallyCompactMetricDecodeBHist (locallyCompactMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def locallyCompactMetricToEventFlow : LocallyCompactMetricUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocallyCompactMetricUp.mk metric point neighbourhood compactWitness totallyBounded
      completeMetric radius transport replay provenance name =>
      [[BMark.b0],
        locallyCompactMetricEncodeBHist metric,
        [BMark.b1, BMark.b0],
        locallyCompactMetricEncodeBHist point,
        [BMark.b1, BMark.b1, BMark.b0],
        locallyCompactMetricEncodeBHist neighbourhood,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locallyCompactMetricEncodeBHist compactWitness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locallyCompactMetricEncodeBHist totallyBounded,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locallyCompactMetricEncodeBHist completeMetric,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locallyCompactMetricEncodeBHist radius,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locallyCompactMetricEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locallyCompactMetricEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        locallyCompactMetricEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locallyCompactMetricEncodeBHist name]

private def locallyCompactMetricRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => locallyCompactMetricRawAt n rest

private def locallyCompactMetricLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => locallyCompactMetricLengthEq n rest

private def locallyCompactMetricFromEventFlow : EventFlow -> Option LocallyCompactMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match locallyCompactMetricLengthEq 22 flow with
      | true =>
          some
            (LocallyCompactMetricUp.mk
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 1 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 3 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 5 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 7 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 9 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 11 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 13 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 15 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 17 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 19 flow))
              (locallyCompactMetricDecodeBHist (locallyCompactMetricRawAt 21 flow)))
      | false => none

private theorem locallyCompactMetric_round_trip :
    ∀ x : LocallyCompactMetricUp,
      locallyCompactMetricFromEventFlow (locallyCompactMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric point neighbourhood compactWitness totallyBounded completeMetric radius transport
      replay provenance name =>
      change
        some
          (LocallyCompactMetricUp.mk
            (locallyCompactMetricDecodeBHist (locallyCompactMetricEncodeBHist metric))
            (locallyCompactMetricDecodeBHist (locallyCompactMetricEncodeBHist point))
            (locallyCompactMetricDecodeBHist
              (locallyCompactMetricEncodeBHist neighbourhood))
            (locallyCompactMetricDecodeBHist
              (locallyCompactMetricEncodeBHist compactWitness))
            (locallyCompactMetricDecodeBHist
              (locallyCompactMetricEncodeBHist totallyBounded))
            (locallyCompactMetricDecodeBHist
              (locallyCompactMetricEncodeBHist completeMetric))
            (locallyCompactMetricDecodeBHist (locallyCompactMetricEncodeBHist radius))
            (locallyCompactMetricDecodeBHist (locallyCompactMetricEncodeBHist transport))
            (locallyCompactMetricDecodeBHist (locallyCompactMetricEncodeBHist replay))
            (locallyCompactMetricDecodeBHist (locallyCompactMetricEncodeBHist provenance))
            (locallyCompactMetricDecodeBHist (locallyCompactMetricEncodeBHist name))) =
        some
          (LocallyCompactMetricUp.mk metric point neighbourhood compactWitness totallyBounded
            completeMetric radius transport replay provenance name)
      rw [locallyCompactMetric_decode_encode_bhist metric,
        locallyCompactMetric_decode_encode_bhist point,
        locallyCompactMetric_decode_encode_bhist neighbourhood,
        locallyCompactMetric_decode_encode_bhist compactWitness,
        locallyCompactMetric_decode_encode_bhist totallyBounded,
        locallyCompactMetric_decode_encode_bhist completeMetric,
        locallyCompactMetric_decode_encode_bhist radius,
        locallyCompactMetric_decode_encode_bhist transport,
        locallyCompactMetric_decode_encode_bhist replay,
        locallyCompactMetric_decode_encode_bhist provenance,
        locallyCompactMetric_decode_encode_bhist name]

private theorem locallyCompactMetricToEventFlow_injective {x y : LocallyCompactMetricUp} :
    locallyCompactMetricToEventFlow x = locallyCompactMetricToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locallyCompactMetricFromEventFlow (locallyCompactMetricToEventFlow x) =
        locallyCompactMetricFromEventFlow (locallyCompactMetricToEventFlow y) :=
    congrArg locallyCompactMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locallyCompactMetric_round_trip x).symm
      (Eq.trans hread (locallyCompactMetric_round_trip y)))

instance locallyCompactMetricBHistCarrier : BHistCarrier LocallyCompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locallyCompactMetricToEventFlow
  fromEventFlow := locallyCompactMetricFromEventFlow

instance locallyCompactMetricChapterTasteGate : ChapterTasteGate LocallyCompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locallyCompactMetricFromEventFlow (locallyCompactMetricToEventFlow x) = some x
    exact locallyCompactMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locallyCompactMetricToEventFlow_injective heq)

theorem LocallyCompactMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, locallyCompactMetricDecodeBHist (locallyCompactMetricEncodeBHist h) = h) ∧
      (∀ x : LocallyCompactMetricUp,
        locallyCompactMetricFromEventFlow (locallyCompactMetricToEventFlow x) = some x) ∧
        (∀ x y : LocallyCompactMetricUp,
          locallyCompactMetricToEventFlow x = locallyCompactMetricToEventFlow y -> x = y) ∧
          locallyCompactMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨locallyCompactMetric_decode_encode_bhist,
      locallyCompactMetric_round_trip,
      by
        intro x y heq
        exact locallyCompactMetricToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocallyCompactMetricUp
