import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealModulusCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealModulusCriterionUp : Type where
  | mk (M S Q W D L E H C P N : BHist) : RealModulusCriterionUp
  deriving DecidableEq

def realModulusCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realModulusCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realModulusCriterionEncodeBHist h

def realModulusCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realModulusCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realModulusCriterionDecodeBHist tail)

private theorem RealModulusCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realModulusCriterionFields : RealModulusCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealModulusCriterionUp.mk M S Q W D L E H C P N => [M, S, Q, W, D, L, E, H, C, P, N]

def realModulusCriterionToEventFlow : RealModulusCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realModulusCriterionFields x).map realModulusCriterionEncodeBHist

private def realModulusCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realModulusCriterionEventAtDefault index rest

def realModulusCriterionFromEventFlow
    (ef : EventFlow) : Option RealModulusCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealModulusCriterionUp.mk
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 0 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 1 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 2 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 3 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 4 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 5 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 6 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 7 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 8 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 9 ef))
      (realModulusCriterionDecodeBHist (realModulusCriterionEventAtDefault 10 ef)))

private theorem RealModulusCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealModulusCriterionUp,
      realModulusCriterionFromEventFlow
          (realModulusCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M S Q W D L E H C P N =>
      change
        some
          (RealModulusCriterionUp.mk
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist M))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist S))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist Q))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist W))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist D))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist L))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist E))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist H))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist C))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist P))
            (realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist N))) =
          some (RealModulusCriterionUp.mk M S Q W D L E H C P N)
      rw [RealModulusCriterionTasteGate_single_carrier_alignment_decode M,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode S,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode Q,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode W,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode D,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode L,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode E,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode H,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode C,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode P,
        RealModulusCriterionTasteGate_single_carrier_alignment_decode N]

private theorem RealModulusCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealModulusCriterionUp} :
    realModulusCriterionToEventFlow x = realModulusCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realModulusCriterionFromEventFlow (realModulusCriterionToEventFlow x) =
        realModulusCriterionFromEventFlow (realModulusCriterionToEventFlow y) :=
    congrArg realModulusCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealModulusCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealModulusCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance realModulusCriterionBHistCarrier : BHistCarrier RealModulusCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realModulusCriterionToEventFlow
  fromEventFlow := realModulusCriterionFromEventFlow

instance realModulusCriterionChapterTasteGate : ChapterTasteGate RealModulusCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realModulusCriterionFromEventFlow (realModulusCriterionToEventFlow x) = some x
    exact RealModulusCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealModulusCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealModulusCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realModulusCriterionChapterTasteGate

theorem RealModulusCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, realModulusCriterionDecodeBHist (realModulusCriterionEncodeBHist h) = h) ∧
      (∀ x : RealModulusCriterionUp,
        realModulusCriterionFromEventFlow (realModulusCriterionToEventFlow x) = some x) ∧
        (∀ x y : RealModulusCriterionUp,
          realModulusCriterionToEventFlow x = realModulusCriterionToEventFlow y → x = y) ∧
          realModulusCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealModulusCriterionTasteGate_single_carrier_alignment_decode,
      RealModulusCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealModulusCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealModulusCriterionUp
