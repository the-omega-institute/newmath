import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionLeftAdjointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionLeftAdjointUp : Type where
  | mk :
      (reflector denseUnit cauchyAdjunction metricAdjunction readback sealRow transport replay
        provenance name : BHist) →
        MetricCompletionLeftAdjointUp
  deriving DecidableEq

private def metricCompletionLeftAdjointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionLeftAdjointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionLeftAdjointEncodeBHist h

private def metricCompletionLeftAdjointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionLeftAdjointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionLeftAdjointDecodeBHist tail)

private theorem metricCompletionLeftAdjointDecodeEncodeBHist :
    ∀ h : BHist, metricCompletionLeftAdjointDecodeBHist
      (metricCompletionLeftAdjointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem metricCompletionLeftAdjoint_mk_congr
    {reflector reflector' denseUnit denseUnit' cauchyAdjunction cauchyAdjunction'
      metricAdjunction metricAdjunction' readback readback' sealRow sealRow' transport
      transport' replay replay' provenance provenance' name name' : BHist}
    (hReflector : reflector' = reflector)
    (hDenseUnit : denseUnit' = denseUnit)
    (hCauchyAdjunction : cauchyAdjunction' = cauchyAdjunction)
    (hMetricAdjunction : metricAdjunction' = metricAdjunction)
    (hReadback : readback' = readback)
    (hSealRow : sealRow' = sealRow)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    MetricCompletionLeftAdjointUp.mk reflector' denseUnit' cauchyAdjunction'
        metricAdjunction' readback' sealRow' transport' replay' provenance' name' =
      MetricCompletionLeftAdjointUp.mk reflector denseUnit cauchyAdjunction metricAdjunction
        readback sealRow transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hReflector
  cases hDenseUnit
  cases hCauchyAdjunction
  cases hMetricAdjunction
  cases hReadback
  cases hSealRow
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

private def metricCompletionLeftAdjointToEventFlow :
    MetricCompletionLeftAdjointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionLeftAdjointUp.mk reflector denseUnit cauchyAdjunction metricAdjunction
      readback sealRow transport replay provenance name =>
      [[BMark.b0],
        metricCompletionLeftAdjointEncodeBHist reflector,
        [BMark.b1, BMark.b0],
        metricCompletionLeftAdjointEncodeBHist denseUnit,
        [BMark.b1, BMark.b1, BMark.b0],
        metricCompletionLeftAdjointEncodeBHist cauchyAdjunction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionLeftAdjointEncodeBHist metricAdjunction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionLeftAdjointEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionLeftAdjointEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionLeftAdjointEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metricCompletionLeftAdjointEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metricCompletionLeftAdjointEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metricCompletionLeftAdjointEncodeBHist name]

private def metricCompletionLeftAdjointFromEventFlow :
    EventFlow → Option MetricCompletionLeftAdjointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | reflector :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | denseUnit :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cauchyAdjunction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | metricAdjunction :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | sealRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | replay :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MetricCompletionLeftAdjointUp.mk
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            reflector)
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            denseUnit)
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            cauchyAdjunction)
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            metricAdjunction)
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            readback)
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            sealRow)
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            transport)
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            replay)
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            provenance)
                                                                                          (metricCompletionLeftAdjointDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ => none

private theorem metricCompletionLeftAdjointRoundTrip :
    ∀ x : MetricCompletionLeftAdjointUp,
      metricCompletionLeftAdjointFromEventFlow
        (metricCompletionLeftAdjointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk reflector denseUnit cauchyAdjunction metricAdjunction readback sealRow transport replay
      provenance name =>
      change
        some
          (MetricCompletionLeftAdjointUp.mk
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist reflector))
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist denseUnit))
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist cauchyAdjunction))
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist metricAdjunction))
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist readback))
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist sealRow))
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist transport))
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist replay))
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist provenance))
            (metricCompletionLeftAdjointDecodeBHist
              (metricCompletionLeftAdjointEncodeBHist name))) =
          some
            (MetricCompletionLeftAdjointUp.mk reflector denseUnit cauchyAdjunction
              metricAdjunction readback sealRow transport replay provenance name)
      exact
        congrArg some
          (metricCompletionLeftAdjoint_mk_congr
            (metricCompletionLeftAdjointDecodeEncodeBHist reflector)
            (metricCompletionLeftAdjointDecodeEncodeBHist denseUnit)
            (metricCompletionLeftAdjointDecodeEncodeBHist cauchyAdjunction)
            (metricCompletionLeftAdjointDecodeEncodeBHist metricAdjunction)
            (metricCompletionLeftAdjointDecodeEncodeBHist readback)
            (metricCompletionLeftAdjointDecodeEncodeBHist sealRow)
            (metricCompletionLeftAdjointDecodeEncodeBHist transport)
            (metricCompletionLeftAdjointDecodeEncodeBHist replay)
            (metricCompletionLeftAdjointDecodeEncodeBHist provenance)
            (metricCompletionLeftAdjointDecodeEncodeBHist name))

private theorem metricCompletionLeftAdjointToEventFlow_injective
    {x y : MetricCompletionLeftAdjointUp} :
    metricCompletionLeftAdjointToEventFlow x =
      metricCompletionLeftAdjointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionLeftAdjointFromEventFlow
          (metricCompletionLeftAdjointToEventFlow x) =
        metricCompletionLeftAdjointFromEventFlow
          (metricCompletionLeftAdjointToEventFlow y) :=
    congrArg metricCompletionLeftAdjointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricCompletionLeftAdjointRoundTrip x).symm
      (Eq.trans hread (metricCompletionLeftAdjointRoundTrip y)))

private def metricCompletionLeftAdjointFields :
    MetricCompletionLeftAdjointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionLeftAdjointUp.mk reflector denseUnit cauchyAdjunction metricAdjunction
      readback sealRow transport replay provenance name =>
      [reflector, denseUnit, cauchyAdjunction, metricAdjunction, readback, sealRow, transport,
        replay, provenance, name]

private theorem metricCompletionLeftAdjoint_field_faithful :
    ∀ x y : MetricCompletionLeftAdjointUp,
      metricCompletionLeftAdjointFields x = metricCompletionLeftAdjointFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk reflector denseUnit cauchyAdjunction metricAdjunction readback sealRow transport replay
      provenance name =>
      cases y with
      | mk reflector' denseUnit' cauchyAdjunction' metricAdjunction' readback' sealRow'
          transport' replay' provenance' name' =>
          cases hfields
          rfl

instance metricCompletionLeftAdjointBHistCarrier :
    BHistCarrier MetricCompletionLeftAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionLeftAdjointToEventFlow
  fromEventFlow := metricCompletionLeftAdjointFromEventFlow

instance metricCompletionLeftAdjointChapterTasteGate :
    ChapterTasteGate MetricCompletionLeftAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricCompletionLeftAdjointFromEventFlow
      (metricCompletionLeftAdjointToEventFlow x) = some x
    exact metricCompletionLeftAdjointRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricCompletionLeftAdjointToEventFlow_injective heq)

instance metricCompletionLeftAdjointFieldFaithful :
    FieldFaithful MetricCompletionLeftAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCompletionLeftAdjointFields
  field_faithful := metricCompletionLeftAdjoint_field_faithful

instance metricCompletionLeftAdjointNontrivial :
    Nontrivial MetricCompletionLeftAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricCompletionLeftAdjointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricCompletionLeftAdjointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricCompletionLeftAdjointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionLeftAdjointChapterTasteGate

theorem MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, metricCompletionLeftAdjointDecodeBHist
      (metricCompletionLeftAdjointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  exact metricCompletionLeftAdjointDecodeEncodeBHist

theorem MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricCompletionLeftAdjointUp,
      metricCompletionLeftAdjointFromEventFlow
        (metricCompletionLeftAdjointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  exact metricCompletionLeftAdjointRoundTrip

theorem MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_injective :
    ∀ x y : MetricCompletionLeftAdjointUp,
      metricCompletionLeftAdjointToEventFlow x =
        metricCompletionLeftAdjointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  exact fun _x _y heq => metricCompletionLeftAdjointToEventFlow_injective heq

theorem MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_empty :
    metricCompletionLeftAdjointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  rfl

theorem MetricCompletionLeftAdjointTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricCompletionLeftAdjointDecodeBHist
        (metricCompletionLeftAdjointEncodeBHist h) = h) ∧
      (∀ x : MetricCompletionLeftAdjointUp,
        metricCompletionLeftAdjointFromEventFlow
          (metricCompletionLeftAdjointToEventFlow x) = some x) ∧
        (∀ x y : MetricCompletionLeftAdjointUp,
          metricCompletionLeftAdjointToEventFlow x =
            metricCompletionLeftAdjointToEventFlow y → x = y) ∧
          metricCompletionLeftAdjointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_decode
      (And.intro MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_round_trip
        (And.intro MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_injective
          MetricCompletionLeftAdjointTasteGate_single_carrier_alignment_empty))

end BEDC.Derived.MetricCompletionLeftAdjointUp
