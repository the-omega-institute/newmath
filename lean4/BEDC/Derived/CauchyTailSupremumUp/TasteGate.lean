import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailSupremumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailSupremumUp : Type where
  | mk (B M W D R E U H C P N : BHist) : CauchyTailSupremumUp
  deriving DecidableEq

def cauchyTailSupremumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailSupremumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailSupremumEncodeBHist h

def cauchyTailSupremumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailSupremumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailSupremumDecodeBHist tail)

private theorem CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailSupremumFields : CauchyTailSupremumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailSupremumUp.mk B M W D R E U H C P N =>
      [B, M, W, D, R, E, U, H, C, P, N]

def cauchyTailSupremumToEventFlow : CauchyTailSupremumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailSupremumFields x).map cauchyTailSupremumEncodeBHist

private def cauchyTailSupremumEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyTailSupremumEventAt index rest

def cauchyTailSupremumFromEventFlow
    (ef : EventFlow) : Option CauchyTailSupremumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyTailSupremumUp.mk
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 0 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 1 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 2 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 3 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 4 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 5 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 6 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 7 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 8 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 9 ef))
      (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEventAt 10 ef)))

private theorem CauchyTailSupremumTasteGate_single_carrier_alignment_round_trip
    (x : CauchyTailSupremumUp) :
    cauchyTailSupremumFromEventFlow (cauchyTailSupremumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B M W D R E U H C P N =>
      change
        some
          (CauchyTailSupremumUp.mk
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist B))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist M))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist W))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist D))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist R))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist E))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist U))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist H))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist C))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist P))
            (cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist N))) =
          some (CauchyTailSupremumUp.mk B M W D R E U H C P N)
      rw [CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode B,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode M,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode W,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode D,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode R,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode E,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode U,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode H,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode C,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode P,
        CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyTailSupremumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTailSupremumUp} :
    cauchyTailSupremumToEventFlow x = cauchyTailSupremumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailSupremumFromEventFlow (cauchyTailSupremumToEventFlow x) =
        cauchyTailSupremumFromEventFlow (cauchyTailSupremumToEventFlow y) :=
    congrArg cauchyTailSupremumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTailSupremumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyTailSupremumTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyTailSupremumTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyTailSupremumUp,
      cauchyTailSupremumFields x = cauchyTailSupremumFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ M₁ W₁ D₁ R₁ E₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ M₂ W₂ D₂ R₂ E₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyTailSupremumBHistCarrier : BHistCarrier CauchyTailSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailSupremumToEventFlow
  fromEventFlow := cauchyTailSupremumFromEventFlow

instance cauchyTailSupremumChapterTasteGate :
    ChapterTasteGate CauchyTailSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailSupremumFromEventFlow (cauchyTailSupremumToEventFlow x) = some x
    exact CauchyTailSupremumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyTailSupremumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyTailSupremumFieldFaithful : FieldFaithful CauchyTailSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailSupremumFields
  field_faithful := CauchyTailSupremumTasteGate_single_carrier_alignment_fields_faithful

theorem CauchyTailSupremumTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailSupremumDecodeBHist (cauchyTailSupremumEncodeBHist h) = h) ∧
      (∀ x : CauchyTailSupremumUp,
        cauchyTailSupremumFromEventFlow (cauchyTailSupremumToEventFlow x) = some x) ∧
        (∀ x y : CauchyTailSupremumUp,
          cauchyTailSupremumToEventFlow x = cauchyTailSupremumToEventFlow y → x = y) ∧
          cauchyTailSupremumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyTailSupremumTasteGate_single_carrier_alignment_decode_encode,
      CauchyTailSupremumTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyTailSupremumTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyTailSupremumUp
