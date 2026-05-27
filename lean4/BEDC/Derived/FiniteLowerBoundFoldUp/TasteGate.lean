import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteLowerBoundFoldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteLowerBoundFoldUp : Type where
  | mk (K P R A B L H C Q N : BHist) : FiniteLowerBoundFoldUp
  deriving DecidableEq

def finiteLowerBoundFoldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteLowerBoundFoldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteLowerBoundFoldEncodeBHist h

def finiteLowerBoundFoldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteLowerBoundFoldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteLowerBoundFoldDecodeBHist tail)

private theorem FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteLowerBoundFoldToEventFlow : FiniteLowerBoundFoldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteLowerBoundFoldUp.mk K P R A B L H C Q N =>
      [[BMark.b1, BMark.b0, BMark.b0],
        finiteLowerBoundFoldEncodeBHist K,
        finiteLowerBoundFoldEncodeBHist P,
        finiteLowerBoundFoldEncodeBHist R,
        finiteLowerBoundFoldEncodeBHist A,
        finiteLowerBoundFoldEncodeBHist B,
        finiteLowerBoundFoldEncodeBHist L,
        finiteLowerBoundFoldEncodeBHist H,
        finiteLowerBoundFoldEncodeBHist C,
        finiteLowerBoundFoldEncodeBHist Q,
        finiteLowerBoundFoldEncodeBHist N]

private def finiteLowerBoundFoldEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteLowerBoundFoldEventAtDefault index rest

def finiteLowerBoundFoldFromEventFlow (ef : EventFlow) : Option FiniteLowerBoundFoldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteLowerBoundFoldUp.mk
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 1 ef))
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 2 ef))
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 3 ef))
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 4 ef))
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 5 ef))
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 6 ef))
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 7 ef))
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 8 ef))
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 9 ef))
      (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEventAtDefault 10 ef)))

private theorem FiniteLowerBoundFoldTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteLowerBoundFoldUp,
      finiteLowerBoundFoldFromEventFlow (finiteLowerBoundFoldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K P R A B L H C Q N =>
      change
        some
          (FiniteLowerBoundFoldUp.mk
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist K))
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist P))
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist R))
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist A))
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist B))
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist L))
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist H))
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist C))
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist Q))
            (finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist N))) =
          some (FiniteLowerBoundFoldUp.mk K P R A B L H C Q N)
      rw [FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode K,
        FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode P,
        FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode R,
        FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode A,
        FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode B,
        FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode L,
        FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode H,
        FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode C,
        FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode Q,
        FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode N]

private theorem FiniteLowerBoundFoldTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteLowerBoundFoldUp} :
    finiteLowerBoundFoldToEventFlow x = finiteLowerBoundFoldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteLowerBoundFoldFromEventFlow (finiteLowerBoundFoldToEventFlow x) =
        finiteLowerBoundFoldFromEventFlow (finiteLowerBoundFoldToEventFlow y) :=
    congrArg finiteLowerBoundFoldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteLowerBoundFoldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteLowerBoundFoldTasteGate_single_carrier_alignment_round_trip y)))

private def finiteLowerBoundFoldFields : FiniteLowerBoundFoldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteLowerBoundFoldUp.mk K P R A B L H C Q N => [K, P, R, A, B, L, H, C, Q, N]

private theorem FiniteLowerBoundFoldTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteLowerBoundFoldUp, finiteLowerBoundFoldFields x = finiteLowerBoundFoldFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 P1 R1 A1 B1 L1 H1 C1 Q1 N1 =>
      cases y with
      | mk K2 P2 R2 A2 B2 L2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance finiteLowerBoundFoldBHistCarrier : BHistCarrier FiniteLowerBoundFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteLowerBoundFoldToEventFlow
  fromEventFlow := finiteLowerBoundFoldFromEventFlow

instance finiteLowerBoundFoldChapterTasteGate : ChapterTasteGate FiniteLowerBoundFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteLowerBoundFoldFromEventFlow (finiteLowerBoundFoldToEventFlow x) = some x
    exact FiniteLowerBoundFoldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteLowerBoundFoldTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteLowerBoundFoldFieldFaithful : FieldFaithful FiniteLowerBoundFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteLowerBoundFoldFields
  field_faithful := FiniteLowerBoundFoldTasteGate_single_carrier_alignment_fields

instance finiteLowerBoundFoldNontrivial : Nontrivial FiniteLowerBoundFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteLowerBoundFoldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteLowerBoundFoldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteLowerBoundFoldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteLowerBoundFoldChapterTasteGate

theorem FiniteLowerBoundFoldTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteLowerBoundFoldUp) ∧
      Nonempty (FieldFaithful FiniteLowerBoundFoldUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteLowerBoundFoldUp) ∧
          (∀ h : BHist,
            finiteLowerBoundFoldDecodeBHist (finiteLowerBoundFoldEncodeBHist h) = h) ∧
            (∀ x : FiniteLowerBoundFoldUp,
              finiteLowerBoundFoldFromEventFlow (finiteLowerBoundFoldToEventFlow x) =
                some x) ∧
              (∀ x y : FiniteLowerBoundFoldUp,
                finiteLowerBoundFoldToEventFlow x = finiteLowerBoundFoldToEventFlow y →
                  x = y) ∧
                finiteLowerBoundFoldEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨finiteLowerBoundFoldChapterTasteGate⟩,
      ⟨finiteLowerBoundFoldFieldFaithful⟩,
      ⟨finiteLowerBoundFoldNontrivial⟩,
      FiniteLowerBoundFoldTasteGate_single_carrier_alignment_decode,
      FiniteLowerBoundFoldTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FiniteLowerBoundFoldTasteGate_single_carrier_alignment_toEventFlow_injective
        heq),
      rfl⟩

end BEDC.Derived.FiniteLowerBoundFoldUp
