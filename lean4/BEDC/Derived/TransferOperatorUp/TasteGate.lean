import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TransferOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TransferOperatorUp : Type where
  | mk (A G S F M R C P N : BHist) : TransferOperatorUp
  deriving DecidableEq

def transferOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: transferOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: transferOperatorEncodeBHist h

def transferOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (transferOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (transferOperatorDecodeBHist tail)

private theorem TransferOperatorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      transferOperatorDecodeBHist
        (transferOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def transferOperatorFields : TransferOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TransferOperatorUp.mk A G S F M R C P N => [A, G, S, F, M, R, C, P, N]

def transferOperatorToEventFlow : TransferOperatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map transferOperatorEncodeBHist (transferOperatorFields x)

def transferOperatorFromEventFlow
    (ef : EventFlow) : Option TransferOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [A, G, S, F, M, R, C, P, N] =>
      some
        (TransferOperatorUp.mk
          (transferOperatorDecodeBHist A)
          (transferOperatorDecodeBHist G)
          (transferOperatorDecodeBHist S)
          (transferOperatorDecodeBHist F)
          (transferOperatorDecodeBHist M)
          (transferOperatorDecodeBHist R)
          (transferOperatorDecodeBHist C)
          (transferOperatorDecodeBHist P)
          (transferOperatorDecodeBHist N))
  | _ => none

private theorem TransferOperatorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TransferOperatorUp,
      transferOperatorFromEventFlow
        (transferOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A G S F M R C P N =>
      change
        some
          (TransferOperatorUp.mk
            (transferOperatorDecodeBHist
              (transferOperatorEncodeBHist A))
            (transferOperatorDecodeBHist
              (transferOperatorEncodeBHist G))
            (transferOperatorDecodeBHist
              (transferOperatorEncodeBHist S))
            (transferOperatorDecodeBHist
              (transferOperatorEncodeBHist F))
            (transferOperatorDecodeBHist
              (transferOperatorEncodeBHist M))
            (transferOperatorDecodeBHist
              (transferOperatorEncodeBHist R))
            (transferOperatorDecodeBHist
              (transferOperatorEncodeBHist C))
            (transferOperatorDecodeBHist
              (transferOperatorEncodeBHist P))
            (transferOperatorDecodeBHist
              (transferOperatorEncodeBHist N))) =
          some (TransferOperatorUp.mk A G S F M R C P N)
      rw [TransferOperatorTasteGate_single_carrier_alignment_decode A,
        TransferOperatorTasteGate_single_carrier_alignment_decode G,
        TransferOperatorTasteGate_single_carrier_alignment_decode S,
        TransferOperatorTasteGate_single_carrier_alignment_decode F,
        TransferOperatorTasteGate_single_carrier_alignment_decode M,
        TransferOperatorTasteGate_single_carrier_alignment_decode R,
        TransferOperatorTasteGate_single_carrier_alignment_decode C,
        TransferOperatorTasteGate_single_carrier_alignment_decode P,
        TransferOperatorTasteGate_single_carrier_alignment_decode N]

private theorem TransferOperatorTasteGate_single_carrier_alignment_injective
    {x y : TransferOperatorUp} :
    transferOperatorToEventFlow x =
      transferOperatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      transferOperatorFromEventFlow
          (transferOperatorToEventFlow x) =
        transferOperatorFromEventFlow
          (transferOperatorToEventFlow y) :=
    congrArg transferOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TransferOperatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TransferOperatorTasteGate_single_carrier_alignment_round_trip y)))

private theorem TransferOperatorTasteGate_single_carrier_alignment_fields :
    ∀ x y : TransferOperatorUp,
      transferOperatorFields x = transferOperatorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 G1 S1 F1 M1 R1 C1 P1 N1 =>
      cases y with
      | mk A2 G2 S2 F2 M2 R2 C2 P2 N2 =>
          cases hfields
          rfl

instance transferOperatorBHistCarrier :
    BHistCarrier TransferOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := transferOperatorToEventFlow
  fromEventFlow := transferOperatorFromEventFlow

instance transferOperatorChapterTasteGate :
    ChapterTasteGate TransferOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      transferOperatorFromEventFlow
        (transferOperatorToEventFlow x) = some x
    exact TransferOperatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TransferOperatorTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate TransferOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  transferOperatorChapterTasteGate

instance transferOperatorFieldFaithful :
    FieldFaithful TransferOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := transferOperatorFields
  field_faithful := TransferOperatorTasteGate_single_carrier_alignment_fields

instance transferOperatorNontrivial :
    Nontrivial TransferOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TransferOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TransferOperatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TransferOperatorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      transferOperatorDecodeBHist
        (transferOperatorEncodeBHist h) = h) ∧
      (∀ x : TransferOperatorUp,
        transferOperatorToEventFlow x =
          List.map transferOperatorEncodeBHist
            (transferOperatorFields x)) ∧
        (∀ x y : TransferOperatorUp,
          transferOperatorFields x = transferOperatorFields y →
            x = y) ∧
          (∃ x y : TransferOperatorUp, x ≠ y) ∧
            transferOperatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨TransferOperatorTasteGate_single_carrier_alignment_decode,
      (fun _ => rfl),
      TransferOperatorTasteGate_single_carrier_alignment_fields,
      ⟨TransferOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        TransferOperatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.TransferOperatorUp
