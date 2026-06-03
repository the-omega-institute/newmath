import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StoneCechCompactificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StoneCechCompactificationUp : Type where
  | mk
      (source generatedOpen boundedRange probeWindow continuousMap compactSeal
        targetSeparation uniformHandoff realValue transport replay provenance
        localName : BHist) :
      StoneCechCompactificationUp

def stoneCechCompactificationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stoneCechCompactificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stoneCechCompactificationEncodeBHist h

def stoneCechCompactificationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stoneCechCompactificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stoneCechCompactificationDecodeBHist tail)

private theorem StoneCechCompactificationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      stoneCechCompactificationDecodeBHist (stoneCechCompactificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stoneCechCompactificationToEventFlow : StoneCechCompactificationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StoneCechCompactificationUp.mk source generatedOpen boundedRange probeWindow
      continuousMap compactSeal targetSeparation uniformHandoff realValue transport replay
      provenance localName =>
      [[BMark.b0],
        stoneCechCompactificationEncodeBHist source,
        [BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist generatedOpen,
        [BMark.b1, BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist boundedRange,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist probeWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist continuousMap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist compactSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist targetSeparation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        stoneCechCompactificationEncodeBHist uniformHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist realValue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stoneCechCompactificationEncodeBHist localName]

private def stoneCechCompactificationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => stoneCechCompactificationEventAtDefault index rest

def stoneCechCompactificationFromEventFlow
    (ef : EventFlow) : Option StoneCechCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StoneCechCompactificationUp.mk
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 1 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 3 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 5 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 7 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 9 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 11 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 13 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 15 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 17 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 19 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 21 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 23 ef))
      (stoneCechCompactificationDecodeBHist (stoneCechCompactificationEventAtDefault 25 ef)))

private theorem StoneCechCompactificationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StoneCechCompactificationUp,
      stoneCechCompactificationFromEventFlow (stoneCechCompactificationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source generatedOpen boundedRange probeWindow continuousMap compactSeal
      targetSeparation uniformHandoff realValue transport replay provenance localName =>
      change
        some
          (StoneCechCompactificationUp.mk
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist source))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist generatedOpen))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist boundedRange))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist probeWindow))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist continuousMap))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist compactSeal))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist targetSeparation))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist uniformHandoff))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist realValue))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist transport))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist replay))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist provenance))
            (stoneCechCompactificationDecodeBHist
              (stoneCechCompactificationEncodeBHist localName))) =
          some
            (StoneCechCompactificationUp.mk source generatedOpen boundedRange probeWindow
              continuousMap compactSeal targetSeparation uniformHandoff realValue transport
              replay provenance localName)
      rw [StoneCechCompactificationTasteGate_single_carrier_alignment_decode source,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode generatedOpen,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode boundedRange,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode probeWindow,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode continuousMap,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode compactSeal,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode targetSeparation,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode uniformHandoff,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode realValue,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode transport,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode replay,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode provenance,
        StoneCechCompactificationTasteGate_single_carrier_alignment_decode localName]

private theorem StoneCechCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StoneCechCompactificationUp} :
    stoneCechCompactificationToEventFlow x = stoneCechCompactificationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stoneCechCompactificationFromEventFlow (stoneCechCompactificationToEventFlow x) =
        stoneCechCompactificationFromEventFlow (stoneCechCompactificationToEventFlow y) :=
    congrArg stoneCechCompactificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (StoneCechCompactificationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (StoneCechCompactificationTasteGate_single_carrier_alignment_round_trip y)))

instance stoneCechCompactificationBHistCarrier : BHistCarrier StoneCechCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stoneCechCompactificationToEventFlow
  fromEventFlow := stoneCechCompactificationFromEventFlow

instance stoneCechCompactificationChapterTasteGate :
    ChapterTasteGate StoneCechCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change stoneCechCompactificationFromEventFlow
      (stoneCechCompactificationToEventFlow x) = some x
    exact StoneCechCompactificationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (StoneCechCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate StoneCechCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stoneCechCompactificationChapterTasteGate

theorem StoneCechCompactificationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      stoneCechCompactificationDecodeBHist (stoneCechCompactificationEncodeBHist h) = h) ∧
      (∀ x : StoneCechCompactificationUp,
        stoneCechCompactificationFromEventFlow (stoneCechCompactificationToEventFlow x) =
          some x) ∧
        (∀ x y : StoneCechCompactificationUp,
          stoneCechCompactificationToEventFlow x = stoneCechCompactificationToEventFlow y →
            x = y) ∧
          stoneCechCompactificationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨StoneCechCompactificationTasteGate_single_carrier_alignment_decode,
      StoneCechCompactificationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        StoneCechCompactificationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.StoneCechCompactificationUp
