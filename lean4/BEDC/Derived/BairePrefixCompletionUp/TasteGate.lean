import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BairePrefixCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BairePrefixCompletionUp : Type where
  | mk (B M S E H C P N : BHist) : BairePrefixCompletionUp
  deriving DecidableEq

def BairePrefixCompletionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: BairePrefixCompletionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: BairePrefixCompletionTasteGate_single_carrier_alignment_encodeBHist h

def BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BairePrefixCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist
          (BairePrefixCompletionTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BairePrefixCompletionTasteGate_single_carrier_alignment_fields :
    BairePrefixCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BairePrefixCompletionUp.mk B M S E H C P N => [B, M, S, E, H, C, P, N]

def BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow :
    BairePrefixCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (BairePrefixCompletionTasteGate_single_carrier_alignment_fields x).map
      BairePrefixCompletionTasteGate_single_carrier_alignment_encodeBHist

def BairePrefixCompletionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BairePrefixCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | B :: M :: S :: E :: H :: C :: P :: N :: [] =>
      some
        (BairePrefixCompletionUp.mk
          (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist B)
          (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist M)
          (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist S)
          (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist E)
          (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist H)
          (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist C)
          (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist P)
          (BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem BairePrefixCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BairePrefixCompletionUp,
      BairePrefixCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B M S E H C P N =>
      simp only [BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow,
        BairePrefixCompletionTasteGate_single_carrier_alignment_fields,
        BairePrefixCompletionTasteGate_single_carrier_alignment_fromEventFlow,
        List.map_cons, List.map_nil,
        BairePrefixCompletionTasteGate_single_carrier_alignment_decode_encode]

private theorem BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BairePrefixCompletionUp} :
    BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow x =
        BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          BairePrefixCompletionTasteGate_single_carrier_alignment_fromEventFlow
            (BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow x) :=
        (BairePrefixCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          BairePrefixCompletionTasteGate_single_carrier_alignment_fromEventFlow
            (BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg BairePrefixCompletionTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := BairePrefixCompletionTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance BairePrefixCompletionTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BairePrefixCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BairePrefixCompletionTasteGate_single_carrier_alignment_fromEventFlow

instance BairePrefixCompletionTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BairePrefixCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BairePrefixCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BairePrefixCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BairePrefixCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BairePrefixCompletionTasteGate_single_carrier_alignment :
    (∀ B M S E H C P N : BHist,
      BairePrefixCompletionTasteGate_single_carrier_alignment_fields
          (BairePrefixCompletionUp.mk B M S E H C P N) =
        [B, M, S, E, H, C, P, N]) ∧
      (∀ h : BHist,
        BairePrefixCompletionTasteGate_single_carrier_alignment_decodeBHist
            (BairePrefixCompletionTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
        BairePrefixCompletionTasteGate_single_carrier_alignment_encodeBHist
            (BHist.e1 BHist.Empty) =
          [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨(fun _ _ _ _ _ _ _ _ => rfl),
      BairePrefixCompletionTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.BairePrefixCompletionUp
