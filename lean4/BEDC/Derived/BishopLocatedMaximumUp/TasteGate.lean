import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedMaximumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedMaximumUp : Type where
  | mk (K F N W R E M H C P L : BHist) : BishopLocatedMaximumUp
  deriving DecidableEq

def bishopLocatedMaximumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedMaximumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedMaximumEncodeBHist h

def bishopLocatedMaximumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedMaximumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedMaximumDecodeBHist tail)

private theorem BishopLocatedMaximumTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedMaximumFields : BishopLocatedMaximumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedMaximumUp.mk K F N W R E M H C P L =>
      [K, F, N, W, R, E, M, H, C, P, L]

def bishopLocatedMaximumToEventFlow : BishopLocatedMaximumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopLocatedMaximumFields x).map bishopLocatedMaximumEncodeBHist

private def bishopLocatedMaximumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedMaximumEventAtDefault index rest

def bishopLocatedMaximumFromEventFlow (ef : EventFlow) : Option BishopLocatedMaximumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedMaximumUp.mk
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 0 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 1 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 2 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 3 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 4 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 5 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 6 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 7 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 8 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 9 ef))
      (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEventAtDefault 10 ef)))

private theorem BishopLocatedMaximumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedMaximumUp,
      bishopLocatedMaximumFromEventFlow (bishopLocatedMaximumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F N W R E M H C P L =>
      change
        some
          (BishopLocatedMaximumUp.mk
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist K))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist F))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist N))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist W))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist R))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist E))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist M))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist H))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist C))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist P))
            (bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist L))) =
          some (BishopLocatedMaximumUp.mk K F N W R E M H C P L)
      rw [BishopLocatedMaximumTasteGate_single_carrier_alignment_decode K,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode F,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode N,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode W,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode R,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode E,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode M,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode H,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode C,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode P,
        BishopLocatedMaximumTasteGate_single_carrier_alignment_decode L]

private theorem BishopLocatedMaximumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopLocatedMaximumUp} :
    bishopLocatedMaximumToEventFlow x = bishopLocatedMaximumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedMaximumFromEventFlow (bishopLocatedMaximumToEventFlow x) =
        bishopLocatedMaximumFromEventFlow (bishopLocatedMaximumToEventFlow y) :=
    congrArg bishopLocatedMaximumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedMaximumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopLocatedMaximumTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopLocatedMaximumTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopLocatedMaximumUp,
      bishopLocatedMaximumFields x = bishopLocatedMaximumFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 N1 W1 R1 E1 M1 H1 C1 P1 L1 =>
      cases y with
      | mk K2 F2 N2 W2 R2 E2 M2 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance bishopLocatedMaximumBHistCarrier : BHistCarrier BishopLocatedMaximumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedMaximumToEventFlow
  fromEventFlow := bishopLocatedMaximumFromEventFlow

instance bishopLocatedMaximumChapterTasteGate : ChapterTasteGate BishopLocatedMaximumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopLocatedMaximumFromEventFlow (bishopLocatedMaximumToEventFlow x) = some x
    exact BishopLocatedMaximumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedMaximumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopLocatedMaximumFieldFaithful : FieldFaithful BishopLocatedMaximumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedMaximumFields
  field_faithful := BishopLocatedMaximumTasteGate_single_carrier_alignment_fields

theorem BishopLocatedMaximumTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopLocatedMaximumDecodeBHist (bishopLocatedMaximumEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate BishopLocatedMaximumUp) ∧
        Nonempty (FieldFaithful BishopLocatedMaximumUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨BishopLocatedMaximumTasteGate_single_carrier_alignment_decode,
      ⟨⟨bishopLocatedMaximumChapterTasteGate⟩, ⟨bishopLocatedMaximumFieldFaithful⟩⟩⟩

end BEDC.Derived.BishopLocatedMaximumUp
