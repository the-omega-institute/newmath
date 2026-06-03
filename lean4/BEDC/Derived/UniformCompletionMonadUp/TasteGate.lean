import BEDC.Derived.UniformCompletionMonadUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionMonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def uniformCompletionMonadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompletionMonadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompletionMonadEncodeBHist h

def uniformCompletionMonadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompletionMonadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompletionMonadDecodeBHist tail)

theorem uniformCompletionMonadDecode_encode_bhist :
    ∀ h : BHist,
      uniformCompletionMonadDecodeBHist (uniformCompletionMonadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCompletionMonadToEventFlow :
    _root_.BEDC.Derived.UniformCompletionMonadUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.UniformCompletionMonadUp.carrier =>
      [uniformCompletionMonadEncodeBHist BHist.Empty]

def uniformCompletionMonadFromEventFlow :
    EventFlow → Option _root_.BEDC.Derived.UniformCompletionMonadUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | event :: rest =>
      match rest with
      | [] =>
          match uniformCompletionMonadDecodeBHist event with
          | BHist.Empty => some _root_.BEDC.Derived.UniformCompletionMonadUp.carrier
          | BHist.e0 _ => none
          | BHist.e1 _ => none
      | _ :: _ => none

private theorem uniformCompletionMonad_round_trip :
    ∀ x : _root_.BEDC.Derived.UniformCompletionMonadUp,
      uniformCompletionMonadFromEventFlow (uniformCompletionMonadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x
  rfl

private theorem uniformCompletionMonadToEventFlow_injective
    {x y : _root_.BEDC.Derived.UniformCompletionMonadUp} :
    uniformCompletionMonadToEventFlow x = uniformCompletionMonadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro _heq
  cases x
  cases y
  rfl

instance uniformCompletionMonadBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.UniformCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompletionMonadToEventFlow
  fromEventFlow := uniformCompletionMonadFromEventFlow

instance uniformCompletionMonadChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.UniformCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformCompletionMonadFromEventFlow (uniformCompletionMonadToEventFlow x) = some x
    exact uniformCompletionMonad_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCompletionMonadToEventFlow_injective heq)

def taste_gate : ChapterTasteGate _root_.BEDC.Derived.UniformCompletionMonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCompletionMonadChapterTasteGate

theorem UniformCompletionMonadTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformCompletionMonadDecodeBHist (uniformCompletionMonadEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier _root_.BEDC.Derived.UniformCompletionMonadUp) ∧
        Nonempty (ChapterTasteGate _root_.BEDC.Derived.UniformCompletionMonadUp) ∧
          uniformCompletionMonadEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate BHistCarrier
  exact
    ⟨uniformCompletionMonadDecode_encode_bhist,
      ⟨uniformCompletionMonadBHistCarrier⟩,
      ⟨uniformCompletionMonadChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.UniformCompletionMonadUp
