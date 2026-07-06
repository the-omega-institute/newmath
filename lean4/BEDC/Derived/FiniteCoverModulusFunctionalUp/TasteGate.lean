import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCoverModulusFunctionalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCoverModulusFunctionalUp : Type where
  | mk
      (compactSource graph coverCells lowerFold dyadicLedger uniformHandoff windowRows
        regseqRead realSeal transport replay provenance name : BHist) :
      FiniteCoverModulusFunctionalUp
  deriving DecidableEq

def finiteCoverModulusFunctionalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCoverModulusFunctionalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCoverModulusFunctionalEncodeBHist h

def finiteCoverModulusFunctionalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCoverModulusFunctionalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCoverModulusFunctionalDecodeBHist tail)

private theorem finiteCoverModulusFunctionalDecode_encode_bhist :
    ∀ h : BHist,
      finiteCoverModulusFunctionalDecodeBHist
        (finiteCoverModulusFunctionalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteCoverModulusFunctionalToEventFlow : FiniteCoverModulusFunctionalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCoverModulusFunctionalUp.mk compactSource graph coverCells lowerFold dyadicLedger
      uniformHandoff windowRows regseqRead realSeal transport replay provenance name =>
      [[BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist compactSource,
        [BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist graph,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist coverCells,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist lowerFold,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist uniformHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist windowRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist regseqRead,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteCoverModulusFunctionalEncodeBHist name]

def finiteCoverModulusFunctionalFromEventFlow :
    EventFlow → Option FiniteCoverModulusFunctionalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: compactSource :: _tag1 :: graph :: _tag2 :: coverCells :: _tag3 ::
      lowerFold :: _tag4 :: dyadicLedger :: _tag5 :: uniformHandoff :: _tag6 ::
      windowRows :: _tag7 :: regseqRead :: _tag8 :: realSeal :: _tag9 :: transport ::
      _tag10 :: replay :: _tag11 :: provenance :: _tag12 :: name :: [] =>
      some
        (FiniteCoverModulusFunctionalUp.mk
          (finiteCoverModulusFunctionalDecodeBHist compactSource)
          (finiteCoverModulusFunctionalDecodeBHist graph)
          (finiteCoverModulusFunctionalDecodeBHist coverCells)
          (finiteCoverModulusFunctionalDecodeBHist lowerFold)
          (finiteCoverModulusFunctionalDecodeBHist dyadicLedger)
          (finiteCoverModulusFunctionalDecodeBHist uniformHandoff)
          (finiteCoverModulusFunctionalDecodeBHist windowRows)
          (finiteCoverModulusFunctionalDecodeBHist regseqRead)
          (finiteCoverModulusFunctionalDecodeBHist realSeal)
          (finiteCoverModulusFunctionalDecodeBHist transport)
          (finiteCoverModulusFunctionalDecodeBHist replay)
          (finiteCoverModulusFunctionalDecodeBHist provenance)
          (finiteCoverModulusFunctionalDecodeBHist name))
  | _ => none

private theorem finiteCoverModulusFunctional_round_trip :
    ∀ x : FiniteCoverModulusFunctionalUp,
      finiteCoverModulusFunctionalFromEventFlow
        (finiteCoverModulusFunctionalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactSource graph coverCells lowerFold dyadicLedger uniformHandoff windowRows
      regseqRead realSeal transport replay provenance name =>
      change
        some
          (FiniteCoverModulusFunctionalUp.mk
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist compactSource))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist graph))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist coverCells))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist lowerFold))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist dyadicLedger))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist uniformHandoff))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist windowRows))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist regseqRead))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist realSeal))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist transport))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist replay))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist provenance))
            (finiteCoverModulusFunctionalDecodeBHist
              (finiteCoverModulusFunctionalEncodeBHist name))) =
          some
            (FiniteCoverModulusFunctionalUp.mk compactSource graph coverCells lowerFold
              dyadicLedger uniformHandoff windowRows regseqRead realSeal transport replay
              provenance name)
      rw [finiteCoverModulusFunctionalDecode_encode_bhist compactSource,
        finiteCoverModulusFunctionalDecode_encode_bhist graph,
        finiteCoverModulusFunctionalDecode_encode_bhist coverCells,
        finiteCoverModulusFunctionalDecode_encode_bhist lowerFold,
        finiteCoverModulusFunctionalDecode_encode_bhist dyadicLedger,
        finiteCoverModulusFunctionalDecode_encode_bhist uniformHandoff,
        finiteCoverModulusFunctionalDecode_encode_bhist windowRows,
        finiteCoverModulusFunctionalDecode_encode_bhist regseqRead,
        finiteCoverModulusFunctionalDecode_encode_bhist realSeal,
        finiteCoverModulusFunctionalDecode_encode_bhist transport,
        finiteCoverModulusFunctionalDecode_encode_bhist replay,
        finiteCoverModulusFunctionalDecode_encode_bhist provenance,
        finiteCoverModulusFunctionalDecode_encode_bhist name]

private theorem finiteCoverModulusFunctionalToEventFlow_injective
    {x y : FiniteCoverModulusFunctionalUp} :
    finiteCoverModulusFunctionalToEventFlow x =
      finiteCoverModulusFunctionalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCoverModulusFunctionalFromEventFlow
          (finiteCoverModulusFunctionalToEventFlow x) =
        finiteCoverModulusFunctionalFromEventFlow
          (finiteCoverModulusFunctionalToEventFlow y) :=
    congrArg finiteCoverModulusFunctionalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteCoverModulusFunctional_round_trip x).symm
      (Eq.trans hread (finiteCoverModulusFunctional_round_trip y)))

instance finiteCoverModulusFunctionalBHistCarrier :
    BHistCarrier FiniteCoverModulusFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCoverModulusFunctionalToEventFlow
  fromEventFlow := finiteCoverModulusFunctionalFromEventFlow

instance finiteCoverModulusFunctionalChapterTasteGate :
    ChapterTasteGate FiniteCoverModulusFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteCoverModulusFunctionalFromEventFlow
        (finiteCoverModulusFunctionalToEventFlow x) = some x
    exact finiteCoverModulusFunctional_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteCoverModulusFunctionalToEventFlow_injective heq)

theorem FiniteCoverModulusFunctionalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteCoverModulusFunctionalDecodeBHist
        (finiteCoverModulusFunctionalEncodeBHist h) = h) ∧
      (∀ x : FiniteCoverModulusFunctionalUp,
        finiteCoverModulusFunctionalFromEventFlow
          (finiteCoverModulusFunctionalToEventFlow x) = some x) ∧
        (∀ x y : FiniteCoverModulusFunctionalUp,
          finiteCoverModulusFunctionalToEventFlow x =
            finiteCoverModulusFunctionalToEventFlow y → x = y) ∧
          finiteCoverModulusFunctionalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteCoverModulusFunctionalDecode_encode_bhist
  · constructor
    · exact finiteCoverModulusFunctional_round_trip
    · constructor
      · intro x y heq
        exact finiteCoverModulusFunctionalToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteCoverModulusFunctionalUp
