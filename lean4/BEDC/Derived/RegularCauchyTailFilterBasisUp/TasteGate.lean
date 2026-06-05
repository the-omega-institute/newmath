import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailFilterBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailFilterBasisUp : Type where
  | mk (R W B D E H C P N : BHist) : RegularCauchyTailFilterBasisUp
  deriving DecidableEq

def regularCauchyTailFilterBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailFilterBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailFilterBasisEncodeBHist h

def regularCauchyTailFilterBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailFilterBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailFilterBasisDecodeBHist tail)

private theorem RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyTailFilterBasisDecodeBHist
          (regularCauchyTailFilterBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTailFilterBasisFields :
    RegularCauchyTailFilterBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailFilterBasisUp.mk R W B D E H C P N => [R, W, B, D, E, H, C, P, N]

def regularCauchyTailFilterBasisToEventFlow :
    RegularCauchyTailFilterBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailFilterBasisFields x).map regularCauchyTailFilterBasisEncodeBHist

private def regularCauchyTailFilterBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTailFilterBasisEventAtDefault index rest

def regularCauchyTailFilterBasisFromEventFlow
    (ef : EventFlow) : Option RegularCauchyTailFilterBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailFilterBasisUp.mk
      (regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEventAtDefault 0 ef))
      (regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEventAtDefault 1 ef))
      (regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEventAtDefault 2 ef))
      (regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEventAtDefault 3 ef))
      (regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEventAtDefault 4 ef))
      (regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEventAtDefault 5 ef))
      (regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEventAtDefault 6 ef))
      (regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEventAtDefault 7 ef))
      (regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEventAtDefault 8 ef)))

private theorem RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyTailFilterBasisUp,
      regularCauchyTailFilterBasisFromEventFlow
          (regularCauchyTailFilterBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W B D E H C P N =>
      change
        some
          (RegularCauchyTailFilterBasisUp.mk
            (regularCauchyTailFilterBasisDecodeBHist
              (regularCauchyTailFilterBasisEncodeBHist R))
            (regularCauchyTailFilterBasisDecodeBHist
              (regularCauchyTailFilterBasisEncodeBHist W))
            (regularCauchyTailFilterBasisDecodeBHist
              (regularCauchyTailFilterBasisEncodeBHist B))
            (regularCauchyTailFilterBasisDecodeBHist
              (regularCauchyTailFilterBasisEncodeBHist D))
            (regularCauchyTailFilterBasisDecodeBHist
              (regularCauchyTailFilterBasisEncodeBHist E))
            (regularCauchyTailFilterBasisDecodeBHist
              (regularCauchyTailFilterBasisEncodeBHist H))
            (regularCauchyTailFilterBasisDecodeBHist
              (regularCauchyTailFilterBasisEncodeBHist C))
            (regularCauchyTailFilterBasisDecodeBHist
              (regularCauchyTailFilterBasisEncodeBHist P))
            (regularCauchyTailFilterBasisDecodeBHist
              (regularCauchyTailFilterBasisEncodeBHist N))) =
          some (RegularCauchyTailFilterBasisUp.mk R W B D E H C P N)
      rw [RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyTailFilterBasisUp} :
    regularCauchyTailFilterBasisToEventFlow x =
        regularCauchyTailFilterBasisToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailFilterBasisFromEventFlow
          (regularCauchyTailFilterBasisToEventFlow x) =
        regularCauchyTailFilterBasisFromEventFlow
          (regularCauchyTailFilterBasisToEventFlow y) :=
    congrArg regularCauchyTailFilterBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyTailFilterBasisUp,
      regularCauchyTailFilterBasisFields x = regularCauchyTailFilterBasisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ W₁ B₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ W₂ B₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyTailFilterBasisBHistCarrier :
    BHistCarrier RegularCauchyTailFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailFilterBasisToEventFlow
  fromEventFlow := regularCauchyTailFilterBasisFromEventFlow

instance regularCauchyTailFilterBasisChapterTasteGate :
    ChapterTasteGate RegularCauchyTailFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailFilterBasisFromEventFlow
          (regularCauchyTailFilterBasisToEventFlow x) = some x
    exact RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyTailFilterBasisFieldFaithful :
    FieldFaithful RegularCauchyTailFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailFilterBasisFields
  field_faithful := RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyTailFilterBasisNontrivial :
    Nontrivial RegularCauchyTailFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailFilterBasisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTailFilterBasisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailFilterBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailFilterBasisChapterTasteGate

theorem RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailFilterBasisDecodeBHist
        (regularCauchyTailFilterBasisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyTailFilterBasisUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyTailFilterBasisUp) ∧
          regularCauchyTailFilterBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RegularCauchyTailFilterBasisTasteGate_single_carrier_alignment_decode_encode,
      ⟨regularCauchyTailFilterBasisBHistCarrier⟩,
      ⟨regularCauchyTailFilterBasisChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyTailFilterBasisUp
