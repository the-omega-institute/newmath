import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionIsometryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionIsometryUp : Type where
  | mk (X U DX DXhat R Q I H C P N : BHist) : CauchyCompletionIsometryUp

def cauchyCompletionIsometryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionIsometryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionIsometryEncodeBHist h

def cauchyCompletionIsometryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionIsometryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionIsometryDecodeBHist tail)

private theorem CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionIsometryToEventFlow : CauchyCompletionIsometryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionIsometryUp.mk X U DX DXhat R Q I H C P N =>
      [cauchyCompletionIsometryEncodeBHist X,
        cauchyCompletionIsometryEncodeBHist U,
        cauchyCompletionIsometryEncodeBHist DX,
        cauchyCompletionIsometryEncodeBHist DXhat,
        cauchyCompletionIsometryEncodeBHist R,
        cauchyCompletionIsometryEncodeBHist Q,
        cauchyCompletionIsometryEncodeBHist I,
        cauchyCompletionIsometryEncodeBHist H,
        cauchyCompletionIsometryEncodeBHist C,
        cauchyCompletionIsometryEncodeBHist P,
        cauchyCompletionIsometryEncodeBHist N]

private def cauchyCompletionIsometryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionIsometryEventAtDefault index rest

def cauchyCompletionIsometryFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionIsometryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionIsometryUp.mk
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 0 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 1 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 2 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 3 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 4 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 5 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 6 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 7 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 8 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 9 ef))
      (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEventAtDefault 10 ef)))

private theorem CauchyCompletionIsometryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionIsometryUp,
      cauchyCompletionIsometryFromEventFlow (cauchyCompletionIsometryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X U DX DXhat R Q I H C P N =>
      change
        some
          (CauchyCompletionIsometryUp.mk
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist X))
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist U))
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist DX))
            (cauchyCompletionIsometryDecodeBHist
              (cauchyCompletionIsometryEncodeBHist DXhat))
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist R))
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist Q))
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist I))
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist H))
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist C))
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist P))
            (cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist N))) =
          some (CauchyCompletionIsometryUp.mk X U DX DXhat R Q I H C P N)
      rw [CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode X,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode U,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode DX,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode DXhat,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode I,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletionIsometryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionIsometryUp} :
    cauchyCompletionIsometryToEventFlow x = cauchyCompletionIsometryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionIsometryFromEventFlow (cauchyCompletionIsometryToEventFlow x) =
        cauchyCompletionIsometryFromEventFlow (cauchyCompletionIsometryToEventFlow y) :=
    congrArg cauchyCompletionIsometryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionIsometryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionIsometryTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionIsometryBHistCarrier :
    BHistCarrier CauchyCompletionIsometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionIsometryToEventFlow
  fromEventFlow := cauchyCompletionIsometryFromEventFlow

instance cauchyCompletionIsometryChapterTasteGate :
    ChapterTasteGate CauchyCompletionIsometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompletionIsometryFromEventFlow (cauchyCompletionIsometryToEventFlow x) =
      some x
    exact CauchyCompletionIsometryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionIsometryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionIsometryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionIsometryChapterTasteGate

theorem CauchyCompletionIsometryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionIsometryDecodeBHist (cauchyCompletionIsometryEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionIsometryUp,
        cauchyCompletionIsometryFromEventFlow (cauchyCompletionIsometryToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyCompletionIsometryUp,
          cauchyCompletionIsometryToEventFlow x =
            cauchyCompletionIsometryToEventFlow y → x = y) ∧
          cauchyCompletionIsometryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCompletionIsometryTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletionIsometryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletionIsometryTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionIsometryUp
