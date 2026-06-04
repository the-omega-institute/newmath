import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySumLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySumLimitUp : Type where
  | mk (X Y S Q D A H C P N : BHist) : CauchySumLimitUp
  deriving DecidableEq

def CauchySumLimitTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchySumLimitTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchySumLimitTasteGate_single_carrier_alignment_encodeBHist h

def CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchySumLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist
      (CauchySumLimitTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchySumLimitTasteGate_single_carrier_alignment_fields : CauchySumLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySumLimitUp.mk X Y S Q D A H C P N => [X, Y, S, Q, D, A, H, C, P, N]

def CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow : CauchySumLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map CauchySumLimitTasteGate_single_carrier_alignment_encodeBHist (CauchySumLimitTasteGate_single_carrier_alignment_fields x)

def CauchySumLimitTasteGate_single_carrier_alignment_fromEventFlow : EventFlow → Option CauchySumLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: Y :: S :: Q :: D :: A :: H :: C :: P :: N :: [] =>
      some
        (CauchySumLimitUp.mk
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist X)
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist Y)
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist S)
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist Q)
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist D)
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist A)
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist H)
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist C)
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist P)
          (CauchySumLimitTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem CauchySumLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchySumLimitUp,
      CauchySumLimitTasteGate_single_carrier_alignment_fromEventFlow (CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y S Q D A H C P N =>
      simp only [CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow, CauchySumLimitTasteGate_single_carrier_alignment_fields,
        CauchySumLimitTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons, List.map_nil,
        CauchySumLimitTasteGate_single_carrier_alignment_decode_encode]

private theorem CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow_injective {x y : CauchySumLimitUp} :
    CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow x = CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchySumLimitTasteGate_single_carrier_alignment_fromEventFlow (CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchySumLimitTasteGate_single_carrier_alignment_fromEventFlow (CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchySumLimitTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchySumLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchySumLimitTasteGate_single_carrier_alignment_round_trip y)))

instance CauchySumLimitTasteGate_single_carrier_alignment_BHistCarrier : BHistCarrier CauchySumLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchySumLimitTasteGate_single_carrier_alignment_fromEventFlow

instance CauchySumLimitTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchySumLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change CauchySumLimitTasteGate_single_carrier_alignment_fromEventFlow (CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow x) =
      some x
    exact CauchySumLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySumLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchySumLimitTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchySumLimitUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact CauchySumLimitTasteGate_single_carrier_alignment_ChapterTasteGate

end BEDC.Derived.CauchySumLimitUp
