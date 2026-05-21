import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniTheoremUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniTheoremUp : Type where
  | mk (X F M W R H C P N : BHist) : DiniTheoremUp
  deriving DecidableEq

def DiniTheoremTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DiniTheoremTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: DiniTheoremTasteGate_single_carrier_alignment_encodeBHist h

def DiniTheoremTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DiniTheoremTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      DiniTheoremTasteGate_single_carrier_alignment_decodeBHist
          (DiniTheoremTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DiniTheoremTasteGate_single_carrier_alignment_fields :
    DiniTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiniTheoremUp.mk X F M W R H C P N => [X, F, M, W, R, H, C, P, N]

def DiniTheoremTasteGate_single_carrier_alignment_toEventFlow :
    DiniTheoremUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (DiniTheoremTasteGate_single_carrier_alignment_fields x).map
      DiniTheoremTasteGate_single_carrier_alignment_encodeBHist

def DiniTheoremTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DiniTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | X :: F :: M :: W :: R :: H :: C :: P :: N :: [] =>
      some
        (DiniTheoremUp.mk
          (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist X)
          (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist F)
          (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist M)
          (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist W)
          (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist R)
          (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist H)
          (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist C)
          (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist P)
          (DiniTheoremTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem DiniTheoremTasteGate_single_carrier_alignment_round_trip :
    forall x : DiniTheoremUp,
      DiniTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (DiniTheoremTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F M W R H C P N =>
      simp only [DiniTheoremTasteGate_single_carrier_alignment_toEventFlow,
        DiniTheoremTasteGate_single_carrier_alignment_fields,
        DiniTheoremTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, DiniTheoremTasteGate_single_carrier_alignment_decode_encode]

private theorem DiniTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DiniTheoremUp} :
    DiniTheoremTasteGate_single_carrier_alignment_toEventFlow x =
        DiniTheoremTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          DiniTheoremTasteGate_single_carrier_alignment_fromEventFlow
            (DiniTheoremTasteGate_single_carrier_alignment_toEventFlow x) :=
        (DiniTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          DiniTheoremTasteGate_single_carrier_alignment_fromEventFlow
            (DiniTheoremTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg DiniTheoremTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := DiniTheoremTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance DiniTheoremTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DiniTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DiniTheoremTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DiniTheoremTasteGate_single_carrier_alignment_fromEventFlow

instance DiniTheoremTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DiniTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DiniTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (DiniTheoremTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DiniTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiniTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DiniTheoremTasteGate_single_carrier_alignment :
    (forall X F M W R H C P N : BHist,
      DiniTheoremTasteGate_single_carrier_alignment_fields
          (DiniTheoremUp.mk X F M W R H C P N) =
        [X, F, M, W, R, H, C, P, N]) ∧
      DiniTheoremTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨(fun _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.DiniTheoremUp.TasteGate
