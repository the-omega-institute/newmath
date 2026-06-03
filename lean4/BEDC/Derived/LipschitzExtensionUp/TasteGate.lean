import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LipschitzExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LipschitzExtensionUp : Type where
  | mk (X A L B F R Q H C P N : BHist) : LipschitzExtensionUp
  deriving DecidableEq

def lipschitzExtensionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lipschitzExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lipschitzExtensionEncodeBHist h

def lipschitzExtensionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lipschitzExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lipschitzExtensionDecodeBHist tail)

private theorem LipschitzExtensionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lipschitzExtensionFields : LipschitzExtensionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LipschitzExtensionUp.mk X A L B F R Q H C P N => [X, A, L, B, F, R, Q, H, C, P, N]

def lipschitzExtensionToEventFlow : LipschitzExtensionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lipschitzExtensionFields x).map lipschitzExtensionEncodeBHist

private def lipschitzExtensionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lipschitzExtensionEventAtDefault index rest

def lipschitzExtensionFromEventFlow (ef : EventFlow) : Option LipschitzExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LipschitzExtensionUp.mk
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 0 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 1 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 2 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 3 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 4 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 5 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 6 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 7 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 8 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 9 ef))
      (lipschitzExtensionDecodeBHist (lipschitzExtensionEventAtDefault 10 ef)))

private theorem LipschitzExtensionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LipschitzExtensionUp,
      lipschitzExtensionFromEventFlow (lipschitzExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A L B F R Q H C P N =>
      change
        some
          (LipschitzExtensionUp.mk
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist X))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist A))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist L))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist B))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist F))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist R))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist Q))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist H))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist C))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist P))
            (lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist N))) =
          some (LipschitzExtensionUp.mk X A L B F R Q H C P N)
      rw [LipschitzExtensionTasteGate_single_carrier_alignment_decode X,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode A,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode L,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode B,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode F,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode R,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode Q,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode H,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode C,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode P,
        LipschitzExtensionTasteGate_single_carrier_alignment_decode N]

private theorem LipschitzExtensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LipschitzExtensionUp} :
    lipschitzExtensionToEventFlow x = lipschitzExtensionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = lipschitzExtensionFromEventFlow (lipschitzExtensionToEventFlow x) :=
        (LipschitzExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      _ = lipschitzExtensionFromEventFlow (lipschitzExtensionToEventFlow y) :=
        congrArg lipschitzExtensionFromEventFlow hxy
      _ = some y := LipschitzExtensionTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem LipschitzExtensionTasteGate_single_carrier_alignment_fields :
    ∀ x y : LipschitzExtensionUp, lipschitzExtensionFields x = lipschitzExtensionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 A1 L1 B1 F1 R1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 A2 L2 B2 F2 R2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance lipschitzExtensionBHistCarrier : BHistCarrier LipschitzExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lipschitzExtensionToEventFlow
  fromEventFlow := lipschitzExtensionFromEventFlow

instance lipschitzExtensionChapterTasteGate : ChapterTasteGate LipschitzExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lipschitzExtensionFromEventFlow (lipschitzExtensionToEventFlow x) = some x
    exact LipschitzExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LipschitzExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance lipschitzExtensionFieldFaithful : FieldFaithful LipschitzExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lipschitzExtensionFields
  field_faithful := LipschitzExtensionTasteGate_single_carrier_alignment_fields

instance lipschitzExtensionNontrivial : Nontrivial LipschitzExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LipschitzExtensionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LipschitzExtensionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LipschitzExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lipschitzExtensionChapterTasteGate

theorem LipschitzExtensionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LipschitzExtensionUp) ∧
      Nonempty (FieldFaithful LipschitzExtensionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LipschitzExtensionUp) ∧
          (∀ h : BHist,
            lipschitzExtensionDecodeBHist (lipschitzExtensionEncodeBHist h) = h) ∧
            (∀ x : LipschitzExtensionUp,
              lipschitzExtensionFromEventFlow (lipschitzExtensionToEventFlow x) = some x) ∧
              (∀ x y : LipschitzExtensionUp,
                lipschitzExtensionToEventFlow x = lipschitzExtensionToEventFlow y -> x = y) ∧
                lipschitzExtensionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨lipschitzExtensionChapterTasteGate⟩,
      ⟨lipschitzExtensionFieldFaithful⟩,
      ⟨lipschitzExtensionNontrivial⟩,
      LipschitzExtensionTasteGate_single_carrier_alignment_decode,
      LipschitzExtensionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LipschitzExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LipschitzExtensionUp
