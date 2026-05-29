import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffCompletionUniversalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffCompletionUniversalUp : Type where
  | mk (M Q S D E L H C P N : BHist) : HausdorffCompletionUniversalUp
  deriving DecidableEq

def hausdorffCompletionUniversalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffCompletionUniversalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffCompletionUniversalEncodeBHist h

def hausdorffCompletionUniversalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffCompletionUniversalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffCompletionUniversalDecodeBHist tail)

private theorem HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hausdorffCompletionUniversalDecodeBHist
          (hausdorffCompletionUniversalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffCompletionUniversalFields : HausdorffCompletionUniversalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffCompletionUniversalUp.mk M Q S D E L H C P N => [M, Q, S, D, E, L, H, C, P, N]

def hausdorffCompletionUniversalToEventFlow : HausdorffCompletionUniversalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hausdorffCompletionUniversalFields x).map hausdorffCompletionUniversalEncodeBHist

def hausdorffCompletionUniversalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffCompletionUniversalEventAt index rest

def hausdorffCompletionUniversalFromEventFlow :
    EventFlow → Option HausdorffCompletionUniversalUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (HausdorffCompletionUniversalUp.mk
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 0 flow))
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 1 flow))
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 2 flow))
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 3 flow))
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 4 flow))
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 5 flow))
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 6 flow))
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 7 flow))
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 8 flow))
          (hausdorffCompletionUniversalDecodeBHist
            (hausdorffCompletionUniversalEventAt 9 flow)))

private theorem HausdorffCompletionUniversalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HausdorffCompletionUniversalUp,
      hausdorffCompletionUniversalFromEventFlow
          (hausdorffCompletionUniversalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M Q S D E L H C P N =>
      change
        some
          (HausdorffCompletionUniversalUp.mk
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist M))
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist Q))
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist S))
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist D))
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist E))
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist L))
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist H))
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist C))
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist P))
            (hausdorffCompletionUniversalDecodeBHist
              (hausdorffCompletionUniversalEncodeBHist N))) =
          some (HausdorffCompletionUniversalUp.mk M Q S D E L H C P N)
      rw [HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode M,
        HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode Q,
        HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode S,
        HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode D,
        HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode E,
        HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode L,
        HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode H,
        HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode C,
        HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode P,
        HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode N]

private theorem HausdorffCompletionUniversalTasteGate_single_carrier_alignment_injective
    {x y : HausdorffCompletionUniversalUp} :
    hausdorffCompletionUniversalToEventFlow x = hausdorffCompletionUniversalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffCompletionUniversalFromEventFlow (hausdorffCompletionUniversalToEventFlow x) =
        hausdorffCompletionUniversalFromEventFlow (hausdorffCompletionUniversalToEventFlow y) :=
    congrArg hausdorffCompletionUniversalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HausdorffCompletionUniversalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HausdorffCompletionUniversalTasteGate_single_carrier_alignment_round_trip y)))

private theorem HausdorffCompletionUniversalTasteGate_single_carrier_alignment_fields :
    ∀ x y : HausdorffCompletionUniversalUp,
      hausdorffCompletionUniversalFields x = hausdorffCompletionUniversalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 Q1 S1 D1 E1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 Q2 S2 D2 E2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hausdorffCompletionUniversalBHistCarrier :
    BHistCarrier HausdorffCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffCompletionUniversalToEventFlow
  fromEventFlow := hausdorffCompletionUniversalFromEventFlow

instance hausdorffCompletionUniversalChapterTasteGate :
    ChapterTasteGate HausdorffCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffCompletionUniversalFromEventFlow
          (hausdorffCompletionUniversalToEventFlow x) = some x
    exact HausdorffCompletionUniversalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffCompletionUniversalTasteGate_single_carrier_alignment_injective heq)

instance hausdorffCompletionUniversalFieldFaithful :
    FieldFaithful HausdorffCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hausdorffCompletionUniversalFields
  field_faithful := HausdorffCompletionUniversalTasteGate_single_carrier_alignment_fields

instance hausdorffCompletionUniversalNontrivial : Nontrivial HausdorffCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffCompletionUniversalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffCompletionUniversalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HausdorffCompletionUniversalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffCompletionUniversalChapterTasteGate

theorem HausdorffCompletionUniversalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hausdorffCompletionUniversalDecodeBHist
          (hausdorffCompletionUniversalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HausdorffCompletionUniversalUp) ∧
        Nonempty (ChapterTasteGate HausdorffCompletionUniversalUp) ∧
          hausdorffCompletionUniversalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨HausdorffCompletionUniversalTasteGate_single_carrier_alignment_decode,
      ⟨hausdorffCompletionUniversalBHistCarrier⟩,
      ⟨hausdorffCompletionUniversalChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.HausdorffCompletionUniversalUp
