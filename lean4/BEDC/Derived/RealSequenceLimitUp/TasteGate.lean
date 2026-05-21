import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSequenceLimitUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSequenceLimitUp : Type where
  | mk (S L W D E H C P N : BHist) : RealSequenceLimitUp
  deriving DecidableEq

def RealSequenceLimitTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RealSequenceLimitTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RealSequenceLimitTasteGate_single_carrier_alignment_encodeBHist h

def RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist
          (RealSequenceLimitTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RealSequenceLimitTasteGate_single_carrier_alignment_fields :
    RealSequenceLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSequenceLimitUp.mk S L W D E H C P N => [S, L, W, D, E, H, C, P, N]

def RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow :
    RealSequenceLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RealSequenceLimitTasteGate_single_carrier_alignment_fields x).map
      RealSequenceLimitTasteGate_single_carrier_alignment_encodeBHist

def RealSequenceLimitTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RealSequenceLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | S :: L :: W :: D :: E :: H :: C :: P :: N :: [] =>
      some
        (RealSequenceLimitUp.mk
          (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist S)
          (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist L)
          (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist W)
          (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist D)
          (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist E)
          (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist H)
          (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist C)
          (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist P)
          (RealSequenceLimitTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem RealSequenceLimitTasteGate_single_carrier_alignment_round_trip :
    forall x : RealSequenceLimitUp,
      RealSequenceLimitTasteGate_single_carrier_alignment_fromEventFlow
          (RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S L W D E H C P N =>
      simp only [RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow,
        RealSequenceLimitTasteGate_single_carrier_alignment_fields,
        RealSequenceLimitTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, RealSequenceLimitTasteGate_single_carrier_alignment_decode_encode]

private theorem RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealSequenceLimitUp} :
    RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow x =
        RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          RealSequenceLimitTasteGate_single_carrier_alignment_fromEventFlow
            (RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow x) :=
        (RealSequenceLimitTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          RealSequenceLimitTasteGate_single_carrier_alignment_fromEventFlow
            (RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg RealSequenceLimitTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := RealSequenceLimitTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance RealSequenceLimitTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RealSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RealSequenceLimitTasteGate_single_carrier_alignment_fromEventFlow

instance RealSequenceLimitTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RealSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RealSequenceLimitTasteGate_single_carrier_alignment_fromEventFlow
          (RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RealSequenceLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RealSequenceLimitTasteGate_single_carrier_alignment :
    (forall S L W D E H C P N : BHist,
      RealSequenceLimitTasteGate_single_carrier_alignment_fields
          (RealSequenceLimitUp.mk S L W D E H C P N) =
        [S, L, W, D, E, H, C, P, N]) ∧
      RealSequenceLimitTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨(fun _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.RealSequenceLimitUp.TasteGate
