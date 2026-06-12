import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusOfUniformConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusOfUniformConvergenceUp : Type where
  | mk (F U M W R E H C P N : BHist) : ModulusOfUniformConvergenceUp
  deriving DecidableEq

def modulusOfUniformConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusOfUniformConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusOfUniformConvergenceEncodeBHist h

def modulusOfUniformConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusOfUniformConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusOfUniformConvergenceDecodeBHist tail)

private theorem ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modulusOfUniformConvergenceToEventFlow :
    ModulusOfUniformConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusOfUniformConvergenceUp.mk F U M W R E H C P N =>
      [[BMark.b0],
        modulusOfUniformConvergenceEncodeBHist F,
        [BMark.b1, BMark.b0],
        modulusOfUniformConvergenceEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformConvergenceEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformConvergenceEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformConvergenceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformConvergenceEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformConvergenceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        modulusOfUniformConvergenceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        modulusOfUniformConvergenceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformConvergenceEncodeBHist N]

private def modulusOfUniformConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => modulusOfUniformConvergenceEventAtDefault index rest

def modulusOfUniformConvergenceFromEventFlow
    (ef : EventFlow) : Option ModulusOfUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ModulusOfUniformConvergenceUp.mk
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 1 ef))
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 3 ef))
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 5 ef))
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 7 ef))
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 9 ef))
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 11 ef))
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 13 ef))
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 15 ef))
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 17 ef))
      (modulusOfUniformConvergenceDecodeBHist
        (modulusOfUniformConvergenceEventAtDefault 19 ef)))

private theorem ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ModulusOfUniformConvergenceUp,
      modulusOfUniformConvergenceFromEventFlow
        (modulusOfUniformConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F U M W R E H C P N =>
      change
        some
          (ModulusOfUniformConvergenceUp.mk
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist F))
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist U))
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist M))
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist W))
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist R))
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist E))
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist H))
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist C))
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist P))
            (modulusOfUniformConvergenceDecodeBHist
              (modulusOfUniformConvergenceEncodeBHist N))) =
          some (ModulusOfUniformConvergenceUp.mk F U M W R E H C P N)
      rw [ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode F,
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode U,
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode M,
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode W,
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode R,
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode C,
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ModulusOfUniformConvergenceUp} :
    modulusOfUniformConvergenceToEventFlow x =
      modulusOfUniformConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusOfUniformConvergenceFromEventFlow (modulusOfUniformConvergenceToEventFlow x) =
        modulusOfUniformConvergenceFromEventFlow (modulusOfUniformConvergenceToEventFlow y) :=
    congrArg modulusOfUniformConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_round_trip y)))

instance modulusOfUniformConvergenceBHistCarrier :
    BHistCarrier ModulusOfUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusOfUniformConvergenceToEventFlow
  fromEventFlow := modulusOfUniformConvergenceFromEventFlow

instance modulusOfUniformConvergenceChapterTasteGate :
    ChapterTasteGate ModulusOfUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      modulusOfUniformConvergenceFromEventFlow
        (modulusOfUniformConvergenceToEventFlow x) = some x
    exact ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance modulusOfUniformConvergenceNontrivial :
    Nontrivial ModulusOfUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ModulusOfUniformConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ModulusOfUniformConvergenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ModulusOfUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modulusOfUniformConvergenceChapterTasteGate

theorem ModulusOfUniformConvergenceTasteGate_single_carrier_alignment :
    ChapterTasteGate ModulusOfUniformConvergenceUp ∧
      (∀ h : BHist,
        modulusOfUniformConvergenceDecodeBHist
          (modulusOfUniformConvergenceEncodeBHist h) = h) ∧
        (∀ x : ModulusOfUniformConvergenceUp,
          modulusOfUniformConvergenceFromEventFlow
            (modulusOfUniformConvergenceToEventFlow x) = some x) ∧
          (∀ x y : ModulusOfUniformConvergenceUp,
            modulusOfUniformConvergenceToEventFlow x =
              modulusOfUniformConvergenceToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨modulusOfUniformConvergenceChapterTasteGate,
      ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_decode_encode,
      ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ModulusOfUniformConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
          heq)⟩

end BEDC.Derived.ModulusOfUniformConvergenceUp
