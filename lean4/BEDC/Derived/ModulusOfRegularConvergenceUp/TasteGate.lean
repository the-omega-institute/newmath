import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusOfRegularConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusOfRegularConvergenceUp : Type where
  | mk (R Q W D E H C P N : BHist) : ModulusOfRegularConvergenceUp

def modulusOfRegularConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusOfRegularConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusOfRegularConvergenceEncodeBHist h

def modulusOfRegularConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusOfRegularConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusOfRegularConvergenceDecodeBHist tail)

private theorem ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modulusOfRegularConvergenceToEventFlow :
    ModulusOfRegularConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusOfRegularConvergenceUp.mk R Q W D E H C P N =>
      ([
        R, Q, W, D, E, H, C, P, N
      ] : List BHist).map modulusOfRegularConvergenceEncodeBHist

private def modulusOfRegularConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => modulusOfRegularConvergenceEventAtDefault index rest

def modulusOfRegularConvergenceFromEventFlow
    (ef : EventFlow) : Option ModulusOfRegularConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ModulusOfRegularConvergenceUp.mk
      (modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEventAtDefault 0 ef))
      (modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEventAtDefault 1 ef))
      (modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEventAtDefault 2 ef))
      (modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEventAtDefault 3 ef))
      (modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEventAtDefault 4 ef))
      (modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEventAtDefault 5 ef))
      (modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEventAtDefault 6 ef))
      (modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEventAtDefault 7 ef))
      (modulusOfRegularConvergenceDecodeBHist
        (modulusOfRegularConvergenceEventAtDefault 8 ef)))

private theorem ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ModulusOfRegularConvergenceUp,
      modulusOfRegularConvergenceFromEventFlow
        (modulusOfRegularConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R Q W D E H C P N =>
      change
        some
          (ModulusOfRegularConvergenceUp.mk
            (modulusOfRegularConvergenceDecodeBHist
              (modulusOfRegularConvergenceEncodeBHist R))
            (modulusOfRegularConvergenceDecodeBHist
              (modulusOfRegularConvergenceEncodeBHist Q))
            (modulusOfRegularConvergenceDecodeBHist
              (modulusOfRegularConvergenceEncodeBHist W))
            (modulusOfRegularConvergenceDecodeBHist
              (modulusOfRegularConvergenceEncodeBHist D))
            (modulusOfRegularConvergenceDecodeBHist
              (modulusOfRegularConvergenceEncodeBHist E))
            (modulusOfRegularConvergenceDecodeBHist
              (modulusOfRegularConvergenceEncodeBHist H))
            (modulusOfRegularConvergenceDecodeBHist
              (modulusOfRegularConvergenceEncodeBHist C))
            (modulusOfRegularConvergenceDecodeBHist
              (modulusOfRegularConvergenceEncodeBHist P))
            (modulusOfRegularConvergenceDecodeBHist
              (modulusOfRegularConvergenceEncodeBHist N))) =
          some (ModulusOfRegularConvergenceUp.mk R Q W D E H C P N)
      rw [ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode R,
        ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode Q,
        ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode W,
        ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode D,
        ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode C,
        ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ModulusOfRegularConvergenceUp} :
    modulusOfRegularConvergenceToEventFlow x =
      modulusOfRegularConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusOfRegularConvergenceFromEventFlow (modulusOfRegularConvergenceToEventFlow x) =
        modulusOfRegularConvergenceFromEventFlow (modulusOfRegularConvergenceToEventFlow y) :=
    congrArg modulusOfRegularConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_round_trip y)))

instance modulusOfRegularConvergenceBHistCarrier :
    BHistCarrier ModulusOfRegularConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusOfRegularConvergenceToEventFlow
  fromEventFlow := modulusOfRegularConvergenceFromEventFlow

instance modulusOfRegularConvergenceChapterTasteGate :
    ChapterTasteGate ModulusOfRegularConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      modulusOfRegularConvergenceFromEventFlow
        (modulusOfRegularConvergenceToEventFlow x) = some x
    exact ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ModulusOfRegularConvergenceTasteGate_single_carrier_alignment :
    (modulusOfRegularConvergenceEncodeBHist BHist.Empty = ([] : List BMark)) ∧
      (∀ h : BHist,
        modulusOfRegularConvergenceDecodeBHist
          (modulusOfRegularConvergenceEncodeBHist h) = h) ∧
        (∀ x : ModulusOfRegularConvergenceUp,
          modulusOfRegularConvergenceFromEventFlow
            (modulusOfRegularConvergenceToEventFlow x) = some x) ∧
          Nonempty (BHistCarrier ModulusOfRegularConvergenceUp) ∧
            Nonempty (ChapterTasteGate ModulusOfRegularConvergenceUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl,
      ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_decode_encode,
      ModulusOfRegularConvergenceTasteGate_single_carrier_alignment_round_trip,
      ⟨modulusOfRegularConvergenceBHistCarrier⟩,
      ⟨modulusOfRegularConvergenceChapterTasteGate⟩⟩

end BEDC.Derived.ModulusOfRegularConvergenceUp
