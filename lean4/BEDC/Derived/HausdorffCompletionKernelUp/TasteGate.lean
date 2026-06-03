import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffCompletionKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffCompletionKernelUp : Type where
  | mk (Q Z F R E H C P N : BHist) : HausdorffCompletionKernelUp
  deriving DecidableEq

def hausdorffCompletionKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffCompletionKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffCompletionKernelEncodeBHist h

def hausdorffCompletionKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffCompletionKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffCompletionKernelDecodeBHist tail)

private theorem HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hausdorffCompletionKernelDecodeBHist
          (hausdorffCompletionKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffCompletionKernelFields : HausdorffCompletionKernelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffCompletionKernelUp.mk Q Z F R E H C P N => [Q, Z, F, R, E, H, C, P, N]

def hausdorffCompletionKernelToEventFlow : HausdorffCompletionKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hausdorffCompletionKernelFields x).map hausdorffCompletionKernelEncodeBHist

def hausdorffCompletionKernelEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffCompletionKernelEventAt index rest

def hausdorffCompletionKernelFromEventFlow :
    EventFlow → Option HausdorffCompletionKernelUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (HausdorffCompletionKernelUp.mk
          (hausdorffCompletionKernelDecodeBHist
            (hausdorffCompletionKernelEventAt 0 flow))
          (hausdorffCompletionKernelDecodeBHist
            (hausdorffCompletionKernelEventAt 1 flow))
          (hausdorffCompletionKernelDecodeBHist
            (hausdorffCompletionKernelEventAt 2 flow))
          (hausdorffCompletionKernelDecodeBHist
            (hausdorffCompletionKernelEventAt 3 flow))
          (hausdorffCompletionKernelDecodeBHist
            (hausdorffCompletionKernelEventAt 4 flow))
          (hausdorffCompletionKernelDecodeBHist
            (hausdorffCompletionKernelEventAt 5 flow))
          (hausdorffCompletionKernelDecodeBHist
            (hausdorffCompletionKernelEventAt 6 flow))
          (hausdorffCompletionKernelDecodeBHist
            (hausdorffCompletionKernelEventAt 7 flow))
          (hausdorffCompletionKernelDecodeBHist
            (hausdorffCompletionKernelEventAt 8 flow)))

private theorem HausdorffCompletionKernelTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HausdorffCompletionKernelUp,
      hausdorffCompletionKernelFromEventFlow
          (hausdorffCompletionKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q Z F R E H C P N =>
      change
        some
          (HausdorffCompletionKernelUp.mk
            (hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist Q))
            (hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist Z))
            (hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist F))
            (hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist R))
            (hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist E))
            (hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist H))
            (hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist C))
            (hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist P))
            (hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist N))) =
          some (HausdorffCompletionKernelUp.mk Q Z F R E H C P N)
      rw [HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode Q,
        HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode Z,
        HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode F,
        HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode R,
        HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode E,
        HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode H,
        HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode C,
        HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode P,
        HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode N]

private theorem HausdorffCompletionKernelTasteGate_single_carrier_alignment_injective
    {x y : HausdorffCompletionKernelUp} :
    hausdorffCompletionKernelToEventFlow x = hausdorffCompletionKernelToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffCompletionKernelFromEventFlow (hausdorffCompletionKernelToEventFlow x) =
        hausdorffCompletionKernelFromEventFlow (hausdorffCompletionKernelToEventFlow y) :=
    congrArg hausdorffCompletionKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HausdorffCompletionKernelTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HausdorffCompletionKernelTasteGate_single_carrier_alignment_round_trip y)))

private theorem HausdorffCompletionKernelTasteGate_single_carrier_alignment_fields :
    ∀ x y : HausdorffCompletionKernelUp,
      hausdorffCompletionKernelFields x = hausdorffCompletionKernelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 Z1 F1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 Z2 F2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hausdorffCompletionKernelBHistCarrier :
    BHistCarrier HausdorffCompletionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffCompletionKernelToEventFlow
  fromEventFlow := hausdorffCompletionKernelFromEventFlow

instance hausdorffCompletionKernelChapterTasteGate :
    ChapterTasteGate HausdorffCompletionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffCompletionKernelFromEventFlow
          (hausdorffCompletionKernelToEventFlow x) = some x
    exact HausdorffCompletionKernelTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffCompletionKernelTasteGate_single_carrier_alignment_injective heq)

instance hausdorffCompletionKernelFieldFaithful :
    FieldFaithful HausdorffCompletionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hausdorffCompletionKernelFields
  field_faithful := HausdorffCompletionKernelTasteGate_single_carrier_alignment_fields

instance hausdorffCompletionKernelNontrivial :
    BEDC.Meta.TasteGate.Nontrivial HausdorffCompletionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffCompletionKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffCompletionKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HausdorffCompletionKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffCompletionKernelChapterTasteGate

theorem HausdorffCompletionKernelTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HausdorffCompletionKernelUp) ∧
      Nonempty (FieldFaithful HausdorffCompletionKernelUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HausdorffCompletionKernelUp) ∧
          (∀ h : BHist,
            hausdorffCompletionKernelDecodeBHist
              (hausdorffCompletionKernelEncodeBHist h) = h) ∧
            hausdorffCompletionKernelEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨hausdorffCompletionKernelChapterTasteGate⟩,
      ⟨hausdorffCompletionKernelFieldFaithful⟩,
      ⟨hausdorffCompletionKernelNontrivial⟩,
      HausdorffCompletionKernelTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.HausdorffCompletionKernelUp
