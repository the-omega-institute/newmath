import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionUnitTriangleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionUnitTriangleUp : Type where
  | mk (U K A E R S D Q H C P N : BHist) : CompletionUnitTriangleUp
  deriving DecidableEq

def completionUnitTriangleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionUnitTriangleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionUnitTriangleEncodeBHist h

def completionUnitTriangleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionUnitTriangleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionUnitTriangleDecodeBHist tail)

private theorem CompletionUnitTriangleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionUnitTriangleFields : CompletionUnitTriangleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionUnitTriangleUp.mk U K A E R S D Q H C P N =>
      [U, K, A, E, R, S, D, Q, H, C, P, N]

def completionUnitTriangleToEventFlow : CompletionUnitTriangleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map completionUnitTriangleEncodeBHist (completionUnitTriangleFields x)

private def completionUnitTriangleEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionUnitTriangleEventAt index rest

def completionUnitTriangleFromEventFlow : EventFlow → Option CompletionUnitTriangleUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CompletionUnitTriangleUp.mk
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 0 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 1 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 2 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 3 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 4 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 5 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 6 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 7 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 8 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 9 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 10 ef))
          (completionUnitTriangleDecodeBHist (completionUnitTriangleEventAt 11 ef)))

private theorem CompletionUnitTriangleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionUnitTriangleUp,
      completionUnitTriangleFromEventFlow (completionUnitTriangleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U K A E R S D Q H C P N =>
      change
        some
          (CompletionUnitTriangleUp.mk
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist U))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist K))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist A))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist E))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist R))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist S))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist D))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist Q))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist H))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist C))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist P))
            (completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist N))) =
          some (CompletionUnitTriangleUp.mk U K A E R S D Q H C P N)
      rw [CompletionUnitTriangleTasteGate_single_carrier_alignment_decode U,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode K,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode A,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode E,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode R,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode S,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode D,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode Q,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode H,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode C,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode P,
        CompletionUnitTriangleTasteGate_single_carrier_alignment_decode N]

private theorem CompletionUnitTriangleTasteGate_single_carrier_alignment_injective
    {x y : CompletionUnitTriangleUp} :
    completionUnitTriangleToEventFlow x = completionUnitTriangleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionUnitTriangleFromEventFlow (completionUnitTriangleToEventFlow x) =
        completionUnitTriangleFromEventFlow (completionUnitTriangleToEventFlow y) :=
    congrArg completionUnitTriangleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompletionUnitTriangleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionUnitTriangleTasteGate_single_carrier_alignment_round_trip y)))

private theorem completionUnitTriangleFieldFaithful :
    ∀ x y : CompletionUnitTriangleUp,
      completionUnitTriangleFields x = completionUnitTriangleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk U1 K1 A1 E1 R1 S1 D1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 K2 A2 E2 R2 S2 D2 Q2 H2 C2 P2 N2 =>
          cases h
          rfl

instance completionUnitTriangleBHistCarrier : BHistCarrier CompletionUnitTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionUnitTriangleToEventFlow
  fromEventFlow := completionUnitTriangleFromEventFlow

instance completionUnitTriangleChapterTasteGate :
    ChapterTasteGate CompletionUnitTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionUnitTriangleFromEventFlow (completionUnitTriangleToEventFlow x) = some x
    exact CompletionUnitTriangleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionUnitTriangleTasteGate_single_carrier_alignment_injective heq)

instance completionUnitTriangleFieldFaithfulInstance :
    FieldFaithful CompletionUnitTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionUnitTriangleFields
  field_faithful := completionUnitTriangleFieldFaithful

instance completionUnitTriangleNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompletionUnitTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionUnitTriangleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CompletionUnitTriangleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompletionUnitTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionUnitTriangleChapterTasteGate

def taste_gate_witness : FieldFaithful CompletionUnitTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionUnitTriangleFieldFaithfulInstance

theorem CompletionUnitTriangleTasteGate_single_carrier_alignment :
    (∀ h : BHist, completionUnitTriangleDecodeBHist (completionUnitTriangleEncodeBHist h) = h) ∧
      completionUnitTriangleFields
          (CompletionUnitTriangleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact ⟨CompletionUnitTriangleTasteGate_single_carrier_alignment_decode, rfl⟩

end BEDC.Derived.CompletionUnitTriangleUp
