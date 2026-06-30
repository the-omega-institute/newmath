import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuousRiemannIntegrabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuousRiemannIntegrabilityUp : Type where
  | mk (F T D J W S R E H C P N : BHist) : ContinuousRiemannIntegrabilityUp
  deriving DecidableEq

def continuousRiemannIntegrabilityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuousRiemannIntegrabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuousRiemannIntegrabilityEncodeBHist h

def continuousRiemannIntegrabilityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuousRiemannIntegrabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuousRiemannIntegrabilityDecodeBHist tail)

private theorem ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def continuousRiemannIntegrabilityFields :
    ContinuousRiemannIntegrabilityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuousRiemannIntegrabilityUp.mk F T D J W S R E H C P N =>
      [F, T, D, J, W, S, R, E, H, C, P, N]

def continuousRiemannIntegrabilityToEventFlow :
    ContinuousRiemannIntegrabilityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (continuousRiemannIntegrabilityFields x).map continuousRiemannIntegrabilityEncodeBHist

private def continuousRiemannIntegrabilityEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => continuousRiemannIntegrabilityEventAt index rest

def continuousRiemannIntegrabilityFromEventFlow
    (ef : EventFlow) : Option ContinuousRiemannIntegrabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuousRiemannIntegrabilityUp.mk
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 0 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 1 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 2 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 3 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 4 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 5 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 6 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 7 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 8 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 9 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 10 ef))
      (continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEventAt 11 ef)))

private theorem ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_round_trip
    (x : ContinuousRiemannIntegrabilityUp) :
    continuousRiemannIntegrabilityFromEventFlow
      (continuousRiemannIntegrabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F T D J W S R E H C P N =>
      change
        some
          (ContinuousRiemannIntegrabilityUp.mk
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist F))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist T))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist D))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist J))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist W))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist S))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist R))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist E))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist H))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist C))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist P))
            (continuousRiemannIntegrabilityDecodeBHist
              (continuousRiemannIntegrabilityEncodeBHist N))) =
          some (ContinuousRiemannIntegrabilityUp.mk F T D J W S R E H C P N)
      rw [ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode F,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode T,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode D,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode J,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode W,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode S,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode R,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode E,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode H,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode C,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode P,
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode N]

private theorem ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContinuousRiemannIntegrabilityUp} :
    continuousRiemannIntegrabilityToEventFlow x =
        continuousRiemannIntegrabilityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuousRiemannIntegrabilityFromEventFlow
          (continuousRiemannIntegrabilityToEventFlow x) =
        continuousRiemannIntegrabilityFromEventFlow
          (continuousRiemannIntegrabilityToEventFlow y) :=
    congrArg continuousRiemannIntegrabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_round_trip y)))

instance continuousRiemannIntegrabilityBHistCarrier :
    BHistCarrier ContinuousRiemannIntegrabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuousRiemannIntegrabilityToEventFlow
  fromEventFlow := continuousRiemannIntegrabilityFromEventFlow

instance continuousRiemannIntegrabilityChapterTasteGate :
    ChapterTasteGate ContinuousRiemannIntegrabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      continuousRiemannIntegrabilityFromEventFlow
        (continuousRiemannIntegrabilityToEventFlow x) = some x
    exact ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ContinuousRiemannIntegrabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuousRiemannIntegrabilityChapterTasteGate

theorem ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      continuousRiemannIntegrabilityDecodeBHist
        (continuousRiemannIntegrabilityEncodeBHist h) = h) ∧
      (forall x : ContinuousRiemannIntegrabilityUp,
        continuousRiemannIntegrabilityFromEventFlow
          (continuousRiemannIntegrabilityToEventFlow x) = some x) ∧
        (forall x y : ContinuousRiemannIntegrabilityUp,
          continuousRiemannIntegrabilityToEventFlow x =
              continuousRiemannIntegrabilityToEventFlow y ->
            x = y) ∧
          continuousRiemannIntegrabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_decode_encode,
      ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ContinuousRiemannIntegrabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContinuousRiemannIntegrabilityUp
