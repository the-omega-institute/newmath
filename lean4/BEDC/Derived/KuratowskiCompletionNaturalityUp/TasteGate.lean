import BEDC.Derived.KuratowskiCompletionNaturalityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiCompletionNaturalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def kuratowskiCompletionNaturalityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiCompletionNaturalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiCompletionNaturalityEncodeBHist h

def kuratowskiCompletionNaturalityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiCompletionNaturalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiCompletionNaturalityDecodeBHist tail)

private theorem KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      kuratowskiCompletionNaturalityDecodeBHist
          (kuratowskiCompletionNaturalityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiCompletionNaturalityFields :
    BEDC.Derived.KuratowskiCompletionNaturalityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.KuratowskiCompletionNaturalityUp.mk sourceMetric kuratowskiRoute metricConsumer
      reflectionWitness realReflectionSeal streamWindow dyadicLedger regularReadback transport
      replay provenance localName =>
      [sourceMetric, kuratowskiRoute, metricConsumer, reflectionWitness, realReflectionSeal,
        streamWindow, dyadicLedger, regularReadback, transport, replay, provenance, localName]

def kuratowskiCompletionNaturalityToEventFlow :
    BEDC.Derived.KuratowskiCompletionNaturalityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.KuratowskiCompletionNaturalityUp.mk sourceMetric kuratowskiRoute metricConsumer
      reflectionWitness realReflectionSeal streamWindow dyadicLedger regularReadback transport
      replay provenance localName =>
      [kuratowskiCompletionNaturalityEncodeBHist sourceMetric,
        kuratowskiCompletionNaturalityEncodeBHist kuratowskiRoute,
        kuratowskiCompletionNaturalityEncodeBHist metricConsumer,
        kuratowskiCompletionNaturalityEncodeBHist reflectionWitness,
        kuratowskiCompletionNaturalityEncodeBHist realReflectionSeal,
        kuratowskiCompletionNaturalityEncodeBHist streamWindow,
        kuratowskiCompletionNaturalityEncodeBHist dyadicLedger,
        kuratowskiCompletionNaturalityEncodeBHist regularReadback,
        kuratowskiCompletionNaturalityEncodeBHist transport,
        kuratowskiCompletionNaturalityEncodeBHist replay,
        kuratowskiCompletionNaturalityEncodeBHist provenance,
        kuratowskiCompletionNaturalityEncodeBHist localName]

private def kuratowskiCompletionNaturalityRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kuratowskiCompletionNaturalityRawAt index rest

def kuratowskiCompletionNaturalityFromEventFlow
    (flow : EventFlow) : Option BEDC.Derived.KuratowskiCompletionNaturalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.KuratowskiCompletionNaturalityUp.mk
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 0 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 1 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 2 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 3 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 4 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 5 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 6 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 7 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 8 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 9 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 10 flow))
      (kuratowskiCompletionNaturalityDecodeBHist
        (kuratowskiCompletionNaturalityRawAt 11 flow)))

private theorem KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_mk_some_congr
    {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : BHist}
    {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : BHist} :
    a1 = b1 ->
      a2 = b2 ->
        a3 = b3 ->
          a4 = b4 ->
            a5 = b5 ->
              a6 = b6 ->
                a7 = b7 ->
                  a8 = b8 ->
                    a9 = b9 ->
                      a10 = b10 ->
                        a11 = b11 ->
                          a12 = b12 ->
                            some
                                (BEDC.Derived.KuratowskiCompletionNaturalityUp.mk a1 a2 a3 a4 a5 a6 a7
                                  a8 a9 a10 a11 a12) =
                              some
                                (BEDC.Derived.KuratowskiCompletionNaturalityUp.mk b1 b2 b3 b4 b5 b6 b7
                                  b8 b9 b10 b11 b12) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  cases h10
  cases h11
  cases h12
  rfl

private theorem KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_round_trip :
    forall x : BEDC.Derived.KuratowskiCompletionNaturalityUp,
      kuratowskiCompletionNaturalityFromEventFlow
          (kuratowskiCompletionNaturalityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk sourceMetric kuratowskiRoute metricConsumer reflectionWitness realReflectionSeal
      streamWindow dyadicLedger regularReadback transport replay provenance localName =>
      exact
        KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_mk_some_congr
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode
            sourceMetric)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode
            kuratowskiRoute)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode
            metricConsumer)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode
            reflectionWitness)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode
            realReflectionSeal)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode
            streamWindow)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode
            dyadicLedger)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode
            regularReadback)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode
            transport)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode replay)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode provenance)
          (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode localName)

private theorem kuratowskiCompletionNaturalityToEventFlow_injective
    {x y : BEDC.Derived.KuratowskiCompletionNaturalityUp} :
    kuratowskiCompletionNaturalityToEventFlow x =
        kuratowskiCompletionNaturalityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          kuratowskiCompletionNaturalityFromEventFlow
            (kuratowskiCompletionNaturalityToEventFlow x) :=
        (KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          kuratowskiCompletionNaturalityFromEventFlow
            (kuratowskiCompletionNaturalityToEventFlow y) :=
        congrArg kuratowskiCompletionNaturalityFromEventFlow hxy
      _ = some y :=
        KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance kuratowskiCompletionNaturalityBHistCarrier :
    BHistCarrier BEDC.Derived.KuratowskiCompletionNaturalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiCompletionNaturalityToEventFlow
  fromEventFlow := kuratowskiCompletionNaturalityFromEventFlow

instance kuratowskiCompletionNaturalityChapterTasteGate :
    ChapterTasteGate BEDC.Derived.KuratowskiCompletionNaturalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kuratowskiCompletionNaturalityFromEventFlow
          (kuratowskiCompletionNaturalityToEventFlow x) =
        some x
    exact KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kuratowskiCompletionNaturalityToEventFlow_injective heq)

def kuratowskiCompletionNaturalityTasteGate :
    ChapterTasteGate BEDC.Derived.KuratowskiCompletionNaturalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kuratowskiCompletionNaturalityChapterTasteGate

theorem KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      kuratowskiCompletionNaturalityDecodeBHist
          (kuratowskiCompletionNaturalityEncodeBHist h) =
        h) /\
      (forall x : BEDC.Derived.KuratowskiCompletionNaturalityUp,
        kuratowskiCompletionNaturalityFromEventFlow
            (kuratowskiCompletionNaturalityToEventFlow x) =
          some x) /\
      (forall x y : BEDC.Derived.KuratowskiCompletionNaturalityUp,
        kuratowskiCompletionNaturalityToEventFlow x =
            kuratowskiCompletionNaturalityToEventFlow y ->
          x = y) /\
      kuratowskiCompletionNaturalityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_decode,
      KuratowskiCompletionNaturalityTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact kuratowskiCompletionNaturalityToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.KuratowskiCompletionNaturalityUp
