import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FormalBallRadiusOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FormalBallRadiusOrderUp : Type where
  | mk (B R D L H C P N : BHist) : FormalBallRadiusOrderUp
  deriving DecidableEq

def formalBallRadiusOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: formalBallRadiusOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: formalBallRadiusOrderEncodeBHist h

def formalBallRadiusOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (formalBallRadiusOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (formalBallRadiusOrderDecodeBHist tail)

private theorem FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def formalBallRadiusOrderFields : FormalBallRadiusOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FormalBallRadiusOrderUp.mk B R D L H C P N => [B, R, D, L, H, C, P, N]

def formalBallRadiusOrderToEventFlow : FormalBallRadiusOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (formalBallRadiusOrderFields x).map formalBallRadiusOrderEncodeBHist

private def formalBallRadiusOrderEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => formalBallRadiusOrderEventAtDefault index rest

def formalBallRadiusOrderFromEventFlow
    (ef : EventFlow) : Option FormalBallRadiusOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FormalBallRadiusOrderUp.mk
      (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEventAtDefault 0 ef))
      (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEventAtDefault 1 ef))
      (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEventAtDefault 2 ef))
      (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEventAtDefault 3 ef))
      (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEventAtDefault 4 ef))
      (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEventAtDefault 5 ef))
      (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEventAtDefault 6 ef))
      (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEventAtDefault 7 ef)))

private theorem FormalBallRadiusOrderTasteGate_single_carrier_alignment_round_trip
    (x : FormalBallRadiusOrderUp) :
    formalBallRadiusOrderFromEventFlow (formalBallRadiusOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B R D L H C P N =>
      change
        some
          (FormalBallRadiusOrderUp.mk
            (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist B))
            (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist R))
            (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist D))
            (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist L))
            (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist H))
            (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist C))
            (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist P))
            (formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist N))) =
          some (FormalBallRadiusOrderUp.mk B R D L H C P N)
      rw [FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode B,
        FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode R,
        FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode D,
        FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode L,
        FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode H,
        FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode C,
        FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode P,
        FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode N]

private theorem FormalBallRadiusOrderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FormalBallRadiusOrderUp} :
    formalBallRadiusOrderToEventFlow x = formalBallRadiusOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      formalBallRadiusOrderFromEventFlow (formalBallRadiusOrderToEventFlow x) =
        formalBallRadiusOrderFromEventFlow (formalBallRadiusOrderToEventFlow y) :=
    congrArg formalBallRadiusOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FormalBallRadiusOrderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FormalBallRadiusOrderTasteGate_single_carrier_alignment_round_trip y)))

instance formalBallRadiusOrderBHistCarrier :
    BHistCarrier FormalBallRadiusOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := formalBallRadiusOrderToEventFlow
  fromEventFlow := formalBallRadiusOrderFromEventFlow

instance formalBallRadiusOrderChapterTasteGate :
    ChapterTasteGate FormalBallRadiusOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change formalBallRadiusOrderFromEventFlow (formalBallRadiusOrderToEventFlow x) = some x
    exact FormalBallRadiusOrderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FormalBallRadiusOrderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FormalBallRadiusOrderTasteGate_single_carrier_alignment :
    (forall h : BHist,
      formalBallRadiusOrderDecodeBHist (formalBallRadiusOrderEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FormalBallRadiusOrderUp) ∧
      Nonempty (ChapterTasteGate FormalBallRadiusOrderUp) ∧
      formalBallRadiusOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact FormalBallRadiusOrderTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨formalBallRadiusOrderBHistCarrier⟩
    · constructor
      · exact ⟨formalBallRadiusOrderChapterTasteGate⟩
      · rfl

end BEDC.Derived.FormalBallRadiusOrderUp
