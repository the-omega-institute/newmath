import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireCategoryTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireCategoryTheoremUp : Type where
  | mk :
      (schedule surface cauchyThread metric windows readback realSeal transport replay
        provenance localName : BHist) →
        BaireCategoryTheoremUp
  deriving DecidableEq

def baireCategoryTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireCategoryTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireCategoryTheoremEncodeBHist h

def baireCategoryTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireCategoryTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireCategoryTheoremDecodeBHist tail)

private theorem baireCategoryTheorem_decode_encode_bhist :
    ∀ h : BHist,
      baireCategoryTheoremDecodeBHist (baireCategoryTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem baireCategoryTheorem_mk_congr
    {schedule schedule' surface surface' cauchyThread cauchyThread' metric metric'
      windows windows' readback readback' realSeal realSeal' transport transport'
      replay replay' provenance provenance' localName localName' : BHist}
    (hSchedule : schedule' = schedule)
    (hSurface : surface' = surface)
    (hCauchyThread : cauchyThread' = cauchyThread)
    (hMetric : metric' = metric)
    (hWindows : windows' = windows)
    (hReadback : readback' = readback)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    BaireCategoryTheoremUp.mk schedule' surface' cauchyThread' metric' windows'
        readback' realSeal' transport' replay' provenance' localName' =
      BaireCategoryTheoremUp.mk schedule surface cauchyThread metric windows readback
        realSeal transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSchedule
  cases hSurface
  cases hCauchyThread
  cases hMetric
  cases hWindows
  cases hReadback
  cases hRealSeal
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def baireCategoryTheoremToEventFlow : BaireCategoryTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BaireCategoryTheoremUp.mk schedule surface cauchyThread metric windows readback
      realSeal transport replay provenance localName =>
      [[BMark.b0],
        baireCategoryTheoremEncodeBHist schedule,
        [BMark.b1, BMark.b0],
        baireCategoryTheoremEncodeBHist surface,
        [BMark.b1, BMark.b1, BMark.b0],
        baireCategoryTheoremEncodeBHist cauchyThread,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        baireCategoryTheoremEncodeBHist metric,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        baireCategoryTheoremEncodeBHist windows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        baireCategoryTheoremEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        baireCategoryTheoremEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        baireCategoryTheoremEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        baireCategoryTheoremEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        baireCategoryTheoremEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        baireCategoryTheoremEncodeBHist localName]

def baireCategoryTheoremFromEventFlow : EventFlow → Option BaireCategoryTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: schedule :: _tag1 :: surface :: _tag2 :: cauchyThread :: _tag3 ::
      metric :: _tag4 :: windows :: _tag5 :: readback :: _tag6 :: realSeal ::
      _tag7 :: transport :: _tag8 :: replay :: _tag9 :: provenance :: _tag10 ::
      localName :: [] =>
        some
          (BaireCategoryTheoremUp.mk
            (baireCategoryTheoremDecodeBHist schedule)
            (baireCategoryTheoremDecodeBHist surface)
            (baireCategoryTheoremDecodeBHist cauchyThread)
            (baireCategoryTheoremDecodeBHist metric)
            (baireCategoryTheoremDecodeBHist windows)
            (baireCategoryTheoremDecodeBHist readback)
            (baireCategoryTheoremDecodeBHist realSeal)
            (baireCategoryTheoremDecodeBHist transport)
            (baireCategoryTheoremDecodeBHist replay)
            (baireCategoryTheoremDecodeBHist provenance)
            (baireCategoryTheoremDecodeBHist localName))
  | _ => none

private theorem baireCategoryTheorem_round_trip :
    ∀ x : BaireCategoryTheoremUp,
      baireCategoryTheoremFromEventFlow
        (baireCategoryTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk schedule surface cauchyThread metric windows readback realSeal transport replay
      provenance localName =>
      change
        some
          (BaireCategoryTheoremUp.mk
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist schedule))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist surface))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist cauchyThread))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist metric))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist windows))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist readback))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist realSeal))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist transport))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist replay))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist provenance))
            (baireCategoryTheoremDecodeBHist
              (baireCategoryTheoremEncodeBHist localName))) =
          some
            (BaireCategoryTheoremUp.mk schedule surface cauchyThread metric windows
              readback realSeal transport replay provenance localName)
      exact
        congrArg some
          (baireCategoryTheorem_mk_congr
            (baireCategoryTheorem_decode_encode_bhist schedule)
            (baireCategoryTheorem_decode_encode_bhist surface)
            (baireCategoryTheorem_decode_encode_bhist cauchyThread)
            (baireCategoryTheorem_decode_encode_bhist metric)
            (baireCategoryTheorem_decode_encode_bhist windows)
            (baireCategoryTheorem_decode_encode_bhist readback)
            (baireCategoryTheorem_decode_encode_bhist realSeal)
            (baireCategoryTheorem_decode_encode_bhist transport)
            (baireCategoryTheorem_decode_encode_bhist replay)
            (baireCategoryTheorem_decode_encode_bhist provenance)
            (baireCategoryTheorem_decode_encode_bhist localName))

private theorem baireCategoryTheoremToEventFlow_injective
    {x y : BaireCategoryTheoremUp} :
    baireCategoryTheoremToEventFlow x = baireCategoryTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireCategoryTheoremFromEventFlow (baireCategoryTheoremToEventFlow x) =
        baireCategoryTheoremFromEventFlow (baireCategoryTheoremToEventFlow y) :=
    congrArg baireCategoryTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (baireCategoryTheorem_round_trip x).symm
      (Eq.trans hread (baireCategoryTheorem_round_trip y)))

instance baireCategoryTheoremBHistCarrier : BHistCarrier BaireCategoryTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireCategoryTheoremToEventFlow
  fromEventFlow := baireCategoryTheoremFromEventFlow

instance baireCategoryTheoremChapterTasteGate :
    ChapterTasteGate BaireCategoryTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      baireCategoryTheoremFromEventFlow
        (baireCategoryTheoremToEventFlow x) = some x
    exact baireCategoryTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (baireCategoryTheoremToEventFlow_injective heq)

theorem BaireCategoryTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, baireCategoryTheoremDecodeBHist
      (baireCategoryTheoremEncodeBHist h) = h) ∧
      baireCategoryTheoremEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ schedule surface cauchyThread metric windows readback realSeal transport replay
            provenance localName : BHist,
          baireCategoryTheoremToEventFlow
              (BaireCategoryTheoremUp.mk schedule surface cauchyThread metric windows readback
                realSeal transport replay provenance localName) =
            [[BMark.b0],
              baireCategoryTheoremEncodeBHist schedule,
              [BMark.b1, BMark.b0],
              baireCategoryTheoremEncodeBHist surface,
              [BMark.b1, BMark.b1, BMark.b0],
              baireCategoryTheoremEncodeBHist cauchyThread,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              baireCategoryTheoremEncodeBHist metric,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              baireCategoryTheoremEncodeBHist windows,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              baireCategoryTheoremEncodeBHist readback,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              baireCategoryTheoremEncodeBHist realSeal,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              baireCategoryTheoremEncodeBHist transport,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b0],
              baireCategoryTheoremEncodeBHist replay,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              baireCategoryTheoremEncodeBHist provenance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              baireCategoryTheoremEncodeBHist localName]) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨baireCategoryTheorem_decode_encode_bhist, rfl, by
    intro schedule surface cauchyThread metric windows readback realSeal transport replay
      provenance localName
    rfl⟩

end BEDC.Derived.BaireCategoryTheoremUp
