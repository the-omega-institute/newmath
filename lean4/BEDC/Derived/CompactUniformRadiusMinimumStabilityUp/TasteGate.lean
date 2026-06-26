import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformRadiusMinimumStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformRadiusMinimumStabilityUp : Type where
  | mk (K B Q S G U H C P N : BHist) : CompactUniformRadiusMinimumStabilityUp
  deriving DecidableEq

def compactUniformRadiusMinimumStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformRadiusMinimumStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformRadiusMinimumStabilityEncodeBHist h

def compactUniformRadiusMinimumStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformRadiusMinimumStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformRadiusMinimumStabilityDecodeBHist tail)

private theorem CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactUniformRadiusMinimumStabilityDecodeBHist
        (compactUniformRadiusMinimumStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformRadiusMinimumStabilityToEventFlow :
    CompactUniformRadiusMinimumStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformRadiusMinimumStabilityUp.mk K B Q S G U H C P N =>
      [compactUniformRadiusMinimumStabilityEncodeBHist K,
        compactUniformRadiusMinimumStabilityEncodeBHist B,
        compactUniformRadiusMinimumStabilityEncodeBHist Q,
        compactUniformRadiusMinimumStabilityEncodeBHist S,
        compactUniformRadiusMinimumStabilityEncodeBHist G,
        compactUniformRadiusMinimumStabilityEncodeBHist U,
        compactUniformRadiusMinimumStabilityEncodeBHist H,
        compactUniformRadiusMinimumStabilityEncodeBHist C,
        compactUniformRadiusMinimumStabilityEncodeBHist P,
        compactUniformRadiusMinimumStabilityEncodeBHist N]

private def compactUniformRadiusMinimumStabilityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => compactUniformRadiusMinimumStabilityRawAt n rest

private def compactUniformRadiusMinimumStabilityLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => compactUniformRadiusMinimumStabilityLengthEq n rest

def compactUniformRadiusMinimumStabilityFromEventFlow :
    EventFlow → Option CompactUniformRadiusMinimumStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match compactUniformRadiusMinimumStabilityLengthEq 10 flow with
      | true =>
          some
            (CompactUniformRadiusMinimumStabilityUp.mk
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 0 flow))
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 1 flow))
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 2 flow))
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 3 flow))
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 4 flow))
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 5 flow))
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 6 flow))
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 7 flow))
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 8 flow))
              (compactUniformRadiusMinimumStabilityDecodeBHist
                (compactUniformRadiusMinimumStabilityRawAt 9 flow)))
      | false => none

private theorem CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformRadiusMinimumStabilityUp,
      compactUniformRadiusMinimumStabilityFromEventFlow
        (compactUniformRadiusMinimumStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K B Q S G U H C P N =>
      change
        some
          (CompactUniformRadiusMinimumStabilityUp.mk
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist K))
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist B))
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist Q))
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist S))
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist G))
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist U))
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist H))
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist C))
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist P))
            (compactUniformRadiusMinimumStabilityDecodeBHist
              (compactUniformRadiusMinimumStabilityEncodeBHist N))) =
          some (CompactUniformRadiusMinimumStabilityUp.mk K B Q S G U H C P N)
      rw [CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode K,
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode B,
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode Q,
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode S,
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode G,
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode U,
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode H,
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode C,
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode P,
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode N]

private theorem CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformRadiusMinimumStabilityUp} :
    compactUniformRadiusMinimumStabilityToEventFlow x =
      compactUniformRadiusMinimumStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformRadiusMinimumStabilityFromEventFlow
          (compactUniformRadiusMinimumStabilityToEventFlow x) =
        compactUniformRadiusMinimumStabilityFromEventFlow
          (compactUniformRadiusMinimumStabilityToEventFlow y) :=
    congrArg compactUniformRadiusMinimumStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformRadiusMinimumStabilityBHistCarrier :
    BHistCarrier CompactUniformRadiusMinimumStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformRadiusMinimumStabilityToEventFlow
  fromEventFlow := compactUniformRadiusMinimumStabilityFromEventFlow

instance compactUniformRadiusMinimumStabilityChapterTasteGate :
    ChapterTasteGate CompactUniformRadiusMinimumStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformRadiusMinimumStabilityFromEventFlow
          (compactUniformRadiusMinimumStabilityToEventFlow x) =
        some x
    exact CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def compactUniformRadiusMinimumStability_taste_gate :
    ChapterTasteGate CompactUniformRadiusMinimumStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformRadiusMinimumStabilityChapterTasteGate

theorem CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        compactUniformRadiusMinimumStabilityDecodeBHist
          (compactUniformRadiusMinimumStabilityEncodeBHist h) = h) ∧
      (∀ x : CompactUniformRadiusMinimumStabilityUp,
        compactUniformRadiusMinimumStabilityFromEventFlow
          (compactUniformRadiusMinimumStabilityToEventFlow x) = some x) ∧
      (∀ x y : CompactUniformRadiusMinimumStabilityUp,
        compactUniformRadiusMinimumStabilityToEventFlow x =
          compactUniformRadiusMinimumStabilityToEventFlow y → x = y) ∧
      compactUniformRadiusMinimumStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_decode,
      CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CompactUniformRadiusMinimumStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.CompactUniformRadiusMinimumStabilityUp
