import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyMeshStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyMeshStabilityUp : Type where
  | mk (M W D R E H C P N : BHist) : CauchyMeshStabilityUp
  deriving DecidableEq

def cauchyMeshStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyMeshStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyMeshStabilityEncodeBHist h

def cauchyMeshStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyMeshStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyMeshStabilityDecodeBHist tail)

private theorem CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyMeshStabilityToEventFlow : CauchyMeshStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyMeshStabilityUp.mk M W D R E H C P N =>
      [[BMark.b0],
        cauchyMeshStabilityEncodeBHist M,
        [BMark.b1, BMark.b0],
        cauchyMeshStabilityEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyMeshStabilityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyMeshStabilityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyMeshStabilityEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyMeshStabilityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyMeshStabilityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyMeshStabilityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyMeshStabilityEncodeBHist N]

private def cauchyMeshStabilityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyMeshStabilityEventAtDefault index rest

def cauchyMeshStabilityFromEventFlow (ef : EventFlow) : Option CauchyMeshStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyMeshStabilityUp.mk
      (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEventAtDefault 1 ef))
      (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEventAtDefault 3 ef))
      (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEventAtDefault 5 ef))
      (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEventAtDefault 7 ef))
      (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEventAtDefault 9 ef))
      (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEventAtDefault 11 ef))
      (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEventAtDefault 13 ef))
      (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEventAtDefault 15 ef))
      (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEventAtDefault 17 ef)))

private theorem CauchyMeshStabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyMeshStabilityUp,
      cauchyMeshStabilityFromEventFlow (cauchyMeshStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M W D R E H C P N =>
      change
        some
          (CauchyMeshStabilityUp.mk
            (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist M))
            (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist W))
            (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist D))
            (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist R))
            (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist E))
            (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist H))
            (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist C))
            (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist P))
            (cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist N))) =
          some (CauchyMeshStabilityUp.mk M W D R E H C P N)
      rw [CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode M,
        CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode W,
        CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode D,
        CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode R,
        CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode E,
        CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode H,
        CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode C,
        CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode P,
        CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyMeshStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyMeshStabilityUp} :
    cauchyMeshStabilityToEventFlow x = cauchyMeshStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyMeshStabilityFromEventFlow (cauchyMeshStabilityToEventFlow x) =
        cauchyMeshStabilityFromEventFlow (cauchyMeshStabilityToEventFlow y) :=
    congrArg cauchyMeshStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyMeshStabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyMeshStabilityTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyMeshStabilityBHistCarrier : BHistCarrier CauchyMeshStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyMeshStabilityToEventFlow
  fromEventFlow := cauchyMeshStabilityFromEventFlow

instance cauchyMeshStabilityChapterTasteGate :
    ChapterTasteGate CauchyMeshStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyMeshStabilityFromEventFlow (cauchyMeshStabilityToEventFlow x) = some x
    exact CauchyMeshStabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyMeshStabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyMeshStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyMeshStabilityDecodeBHist (cauchyMeshStabilityEncodeBHist h) = h) ∧
      (∀ x : CauchyMeshStabilityUp,
        cauchyMeshStabilityFromEventFlow (cauchyMeshStabilityToEventFlow x) = some x) ∧
        (∀ x y : CauchyMeshStabilityUp,
          cauchyMeshStabilityToEventFlow x = cauchyMeshStabilityToEventFlow y → x = y) ∧
          cauchyMeshStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyMeshStabilityTasteGate_single_carrier_alignment_decode_encode,
      CauchyMeshStabilityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyMeshStabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyMeshStabilityUp
