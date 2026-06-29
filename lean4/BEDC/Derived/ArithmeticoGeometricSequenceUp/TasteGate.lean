import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArithmeticoGeometricSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArithmeticoGeometricSequenceUp : Type where
  | mk (I M G W R E H C P N : BHist) : ArithmeticoGeometricSequenceUp
  deriving DecidableEq

def arithmeticoGeometricSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: arithmeticoGeometricSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: arithmeticoGeometricSequenceEncodeBHist h

def arithmeticoGeometricSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (arithmeticoGeometricSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (arithmeticoGeometricSequenceDecodeBHist tail)

private theorem arithmeticoGeometricSequence_decode_encode :
    ∀ h : BHist,
      arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def arithmeticoGeometricSequenceFields :
    ArithmeticoGeometricSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArithmeticoGeometricSequenceUp.mk I M G W R E H C P N =>
      [I, M, G, W, R, E, H, C, P, N]

def arithmeticoGeometricSequenceToEventFlow :
    ArithmeticoGeometricSequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (arithmeticoGeometricSequenceFields x).map
      arithmeticoGeometricSequenceEncodeBHist

private def arithmeticoGeometricSequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => arithmeticoGeometricSequenceEventAt index rest

def arithmeticoGeometricSequenceFromEventFlow
    (ef : EventFlow) : Option ArithmeticoGeometricSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArithmeticoGeometricSequenceUp.mk
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 0 ef))
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 1 ef))
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 2 ef))
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 3 ef))
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 4 ef))
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 5 ef))
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 6 ef))
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 7 ef))
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 8 ef))
      (arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEventAt 9 ef)))

private theorem arithmeticoGeometricSequence_round_trip :
    ∀ x : ArithmeticoGeometricSequenceUp,
      arithmeticoGeometricSequenceFromEventFlow
        (arithmeticoGeometricSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M G W R E H C P N =>
      change
        some
          (ArithmeticoGeometricSequenceUp.mk
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist I))
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist M))
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist G))
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist W))
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist R))
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist E))
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist H))
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist C))
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist P))
            (arithmeticoGeometricSequenceDecodeBHist
              (arithmeticoGeometricSequenceEncodeBHist N))) =
          some (ArithmeticoGeometricSequenceUp.mk I M G W R E H C P N)
      rw [arithmeticoGeometricSequence_decode_encode I,
        arithmeticoGeometricSequence_decode_encode M,
        arithmeticoGeometricSequence_decode_encode G,
        arithmeticoGeometricSequence_decode_encode W,
        arithmeticoGeometricSequence_decode_encode R,
        arithmeticoGeometricSequence_decode_encode E,
        arithmeticoGeometricSequence_decode_encode H,
        arithmeticoGeometricSequence_decode_encode C,
        arithmeticoGeometricSequence_decode_encode P,
        arithmeticoGeometricSequence_decode_encode N]

private theorem arithmeticoGeometricSequenceToEventFlow_injective
    {x y : ArithmeticoGeometricSequenceUp} :
    arithmeticoGeometricSequenceToEventFlow x =
      arithmeticoGeometricSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      arithmeticoGeometricSequenceFromEventFlow
          (arithmeticoGeometricSequenceToEventFlow x) =
        arithmeticoGeometricSequenceFromEventFlow
          (arithmeticoGeometricSequenceToEventFlow y) :=
    congrArg arithmeticoGeometricSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (arithmeticoGeometricSequence_round_trip x).symm
      (Eq.trans hread (arithmeticoGeometricSequence_round_trip y)))

instance arithmeticoGeometricSequenceBHistCarrier :
    BHistCarrier ArithmeticoGeometricSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := arithmeticoGeometricSequenceToEventFlow
  fromEventFlow := arithmeticoGeometricSequenceFromEventFlow

instance arithmeticoGeometricSequenceChapterTasteGate :
    ChapterTasteGate ArithmeticoGeometricSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      arithmeticoGeometricSequenceFromEventFlow
        (arithmeticoGeometricSequenceToEventFlow x) = some x
    exact arithmeticoGeometricSequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (arithmeticoGeometricSequenceToEventFlow_injective heq)

theorem ArithmeticoGeometricSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      arithmeticoGeometricSequenceDecodeBHist
        (arithmeticoGeometricSequenceEncodeBHist h) = h) ∧
      (∀ x : ArithmeticoGeometricSequenceUp,
        arithmeticoGeometricSequenceFromEventFlow
          (arithmeticoGeometricSequenceToEventFlow x) = some x) ∧
      (∀ x y : ArithmeticoGeometricSequenceUp,
        arithmeticoGeometricSequenceToEventFlow x =
          arithmeticoGeometricSequenceToEventFlow y -> x = y) ∧
      arithmeticoGeometricSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨arithmeticoGeometricSequence_decode_encode,
      arithmeticoGeometricSequence_round_trip,
      by
        intro x y heq
        exact arithmeticoGeometricSequenceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ArithmeticoGeometricSequenceUp
