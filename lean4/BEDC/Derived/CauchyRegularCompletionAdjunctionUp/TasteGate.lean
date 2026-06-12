import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRegularCompletionAdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRegularCompletionAdjunctionUp : Type where
  | mk (F R W D L U H C P N : BHist) : CauchyRegularCompletionAdjunctionUp

def cauchyRegularCompletionAdjunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRegularCompletionAdjunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRegularCompletionAdjunctionEncodeBHist h

def cauchyRegularCompletionAdjunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRegularCompletionAdjunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRegularCompletionAdjunctionDecodeBHist tail)

private theorem CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyRegularCompletionAdjunctionDecodeBHist
          (cauchyRegularCompletionAdjunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRegularCompletionAdjunctionToEventFlow :
    CauchyRegularCompletionAdjunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRegularCompletionAdjunctionUp.mk F R W D L U H C P N =>
      [cauchyRegularCompletionAdjunctionEncodeBHist F,
        cauchyRegularCompletionAdjunctionEncodeBHist R,
        cauchyRegularCompletionAdjunctionEncodeBHist W,
        cauchyRegularCompletionAdjunctionEncodeBHist D,
        cauchyRegularCompletionAdjunctionEncodeBHist L,
        cauchyRegularCompletionAdjunctionEncodeBHist U,
        cauchyRegularCompletionAdjunctionEncodeBHist H,
        cauchyRegularCompletionAdjunctionEncodeBHist C,
        cauchyRegularCompletionAdjunctionEncodeBHist P,
        cauchyRegularCompletionAdjunctionEncodeBHist N]

def cauchyRegularCompletionAdjunctionFromEventFlow :
    EventFlow → Option CauchyRegularCompletionAdjunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: R :: W :: D :: L :: U :: H :: C :: P :: N :: [] =>
      some
        (CauchyRegularCompletionAdjunctionUp.mk
          (cauchyRegularCompletionAdjunctionDecodeBHist F)
          (cauchyRegularCompletionAdjunctionDecodeBHist R)
          (cauchyRegularCompletionAdjunctionDecodeBHist W)
          (cauchyRegularCompletionAdjunctionDecodeBHist D)
          (cauchyRegularCompletionAdjunctionDecodeBHist L)
          (cauchyRegularCompletionAdjunctionDecodeBHist U)
          (cauchyRegularCompletionAdjunctionDecodeBHist H)
          (cauchyRegularCompletionAdjunctionDecodeBHist C)
          (cauchyRegularCompletionAdjunctionDecodeBHist P)
          (cauchyRegularCompletionAdjunctionDecodeBHist N))
  | _ => none

private theorem CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRegularCompletionAdjunctionUp,
      cauchyRegularCompletionAdjunctionFromEventFlow
          (cauchyRegularCompletionAdjunctionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F R W D L U H C P N =>
      rw [cauchyRegularCompletionAdjunctionToEventFlow,
        cauchyRegularCompletionAdjunctionFromEventFlow,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode F,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode R,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode W,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode D,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode L,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode U,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode H,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode C,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode P,
        CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_decode N]

private theorem CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_injective
    {x y : CauchyRegularCompletionAdjunctionUp} :
    cauchyRegularCompletionAdjunctionToEventFlow x =
        cauchyRegularCompletionAdjunctionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRegularCompletionAdjunctionFromEventFlow
          (cauchyRegularCompletionAdjunctionToEventFlow x) =
        cauchyRegularCompletionAdjunctionFromEventFlow
          (cauchyRegularCompletionAdjunctionToEventFlow y) :=
    congrArg cauchyRegularCompletionAdjunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyRegularCompletionAdjunctionBHistCarrier :
    BHistCarrier CauchyRegularCompletionAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRegularCompletionAdjunctionToEventFlow
  fromEventFlow := cauchyRegularCompletionAdjunctionFromEventFlow

instance cauchyRegularCompletionAdjunctionChapterTasteGate :
    ChapterTasteGate CauchyRegularCompletionAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyRegularCompletionAdjunctionFromEventFlow
          (cauchyRegularCompletionAdjunctionToEventFlow x) =
        some x
    exact CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment_injective heq)

theorem CauchyRegularCompletionAdjunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyRegularCompletionAdjunctionDecodeBHist
          (cauchyRegularCompletionAdjunctionEncodeBHist h) = h) ∧
      cauchyRegularCompletionAdjunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · rfl

end BEDC.Derived.CauchyRegularCompletionAdjunctionUp
