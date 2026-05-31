import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteNetEquicontinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteNetEquicontinuityUp : Type where
  | mk (K F B R M U H C P N : BHist) : FiniteNetEquicontinuityUp
  deriving DecidableEq

def finiteNetEquicontinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteNetEquicontinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteNetEquicontinuityEncodeBHist h

def finiteNetEquicontinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteNetEquicontinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteNetEquicontinuityDecodeBHist tail)

private theorem FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteNetEquicontinuityFields : FiniteNetEquicontinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteNetEquicontinuityUp.mk K F B R M U H C P N => [K, F, B, R, M, U, H, C, P, N]

def finiteNetEquicontinuityToEventFlow : FiniteNetEquicontinuityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteNetEquicontinuityFields x).map finiteNetEquicontinuityEncodeBHist

private def finiteNetEquicontinuityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteNetEquicontinuityEventAtDefault index rest

def finiteNetEquicontinuityFromEventFlow (ef : EventFlow) :
    Option FiniteNetEquicontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteNetEquicontinuityUp.mk
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 0 ef))
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 1 ef))
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 2 ef))
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 3 ef))
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 4 ef))
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 5 ef))
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 6 ef))
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 7 ef))
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 8 ef))
      (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEventAtDefault 9 ef)))

private theorem FiniteNetEquicontinuityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteNetEquicontinuityUp,
      finiteNetEquicontinuityFromEventFlow
        (finiteNetEquicontinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F B R M U H C P N =>
      change
        some
          (FiniteNetEquicontinuityUp.mk
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist K))
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist F))
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist B))
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist R))
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist M))
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist U))
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist H))
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist C))
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist P))
            (finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist N))) =
          some (FiniteNetEquicontinuityUp.mk K F B R M U H C P N)
      rw [FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode K,
        FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode F,
        FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode B,
        FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode R,
        FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode M,
        FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode U,
        FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode H,
        FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode C,
        FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode P,
        FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode N]

private theorem FiniteNetEquicontinuityTasteGate_single_carrier_alignment_injective
    {x y : FiniteNetEquicontinuityUp} :
    finiteNetEquicontinuityToEventFlow x =
      finiteNetEquicontinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteNetEquicontinuityFromEventFlow (finiteNetEquicontinuityToEventFlow x) =
        finiteNetEquicontinuityFromEventFlow (finiteNetEquicontinuityToEventFlow y) :=
    congrArg finiteNetEquicontinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteNetEquicontinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteNetEquicontinuityTasteGate_single_carrier_alignment_round_trip y)))

private theorem finiteNetEquicontinuityFields_faithful :
    ∀ x y : FiniteNetEquicontinuityUp,
      finiteNetEquicontinuityFields x = finiteNetEquicontinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ B₁ R₁ M₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ B₂ R₂ M₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance finiteNetEquicontinuityBHistCarrier :
    BHistCarrier FiniteNetEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteNetEquicontinuityToEventFlow
  fromEventFlow := finiteNetEquicontinuityFromEventFlow

instance finiteNetEquicontinuityChapterTasteGate :
    ChapterTasteGate FiniteNetEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteNetEquicontinuityFromEventFlow
        (finiteNetEquicontinuityToEventFlow x) = some x
    exact FiniteNetEquicontinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteNetEquicontinuityTasteGate_single_carrier_alignment_injective heq)

instance finiteNetEquicontinuityFieldFaithful :
    FieldFaithful FiniteNetEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteNetEquicontinuityFields
  field_faithful := finiteNetEquicontinuityFields_faithful

instance finiteNetEquicontinuityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteNetEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteNetEquicontinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteNetEquicontinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def finiteNetEquicontinuityTasteGate :
    ChapterTasteGate FiniteNetEquicontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteNetEquicontinuityChapterTasteGate

theorem FiniteNetEquicontinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteNetEquicontinuityDecodeBHist (finiteNetEquicontinuityEncodeBHist h) = h) ∧
      (∀ x : FiniteNetEquicontinuityUp,
        finiteNetEquicontinuityFromEventFlow
          (finiteNetEquicontinuityToEventFlow x) = some x) ∧
      (∀ x y : FiniteNetEquicontinuityUp,
        finiteNetEquicontinuityToEventFlow x =
          finiteNetEquicontinuityToEventFlow y → x = y) ∧
      finiteNetEquicontinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact FiniteNetEquicontinuityTasteGate_single_carrier_alignment_decode
  constructor
  · exact FiniteNetEquicontinuityTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact FiniteNetEquicontinuityTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.FiniteNetEquicontinuityUp
