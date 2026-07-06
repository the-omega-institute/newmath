import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyFilterBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyFilterBasisUp : Type where
  | mk (F W D R Q H C P N : BHist) : RealCauchyFilterBasisUp
  deriving DecidableEq

def realCauchyFilterBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyFilterBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyFilterBasisEncodeBHist h

def realCauchyFilterBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyFilterBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyFilterBasisDecodeBHist tail)

private theorem RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyFilterBasisFields : RealCauchyFilterBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyFilterBasisUp.mk F W D R Q H C P N => [F, W, D, R, Q, H, C, P, N]

def realCauchyFilterBasisToEventFlow : RealCauchyFilterBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realCauchyFilterBasisFields x).map realCauchyFilterBasisEncodeBHist

private def realCauchyFilterBasisEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCauchyFilterBasisEventAt index rest

def realCauchyFilterBasisFromEventFlow (ef : EventFlow) :
    Option RealCauchyFilterBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealCauchyFilterBasisUp.mk
      (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEventAt 0 ef))
      (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEventAt 1 ef))
      (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEventAt 2 ef))
      (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEventAt 3 ef))
      (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEventAt 4 ef))
      (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEventAt 5 ef))
      (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEventAt 6 ef))
      (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEventAt 7 ef))
      (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEventAt 8 ef)))

private theorem RealCauchyFilterBasisTasteGate_single_carrier_alignment_round_trip
    (x : RealCauchyFilterBasisUp) :
    realCauchyFilterBasisFromEventFlow (realCauchyFilterBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F W D R Q H C P N =>
      change
        some
          (RealCauchyFilterBasisUp.mk
            (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist F))
            (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist W))
            (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist D))
            (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist R))
            (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist Q))
            (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist H))
            (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist C))
            (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist P))
            (realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist N))) =
          some (RealCauchyFilterBasisUp.mk F W D R Q H C P N)
      rw [RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode F,
        RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode W,
        RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode D,
        RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode R,
        RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode Q,
        RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode H,
        RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode C,
        RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode P,
        RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealCauchyFilterBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealCauchyFilterBasisUp} :
    realCauchyFilterBasisToEventFlow x = realCauchyFilterBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyFilterBasisFromEventFlow (realCauchyFilterBasisToEventFlow x) =
        realCauchyFilterBasisFromEventFlow (realCauchyFilterBasisToEventFlow y) :=
    congrArg realCauchyFilterBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealCauchyFilterBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealCauchyFilterBasisTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealCauchyFilterBasisTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealCauchyFilterBasisUp,
      realCauchyFilterBasisFields x = realCauchyFilterBasisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ W₁ D₁ R₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ W₂ D₂ R₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance realCauchyFilterBasisBHistCarrier : BHistCarrier RealCauchyFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyFilterBasisToEventFlow
  fromEventFlow := realCauchyFilterBasisFromEventFlow

instance realCauchyFilterBasisChapterTasteGate :
    ChapterTasteGate RealCauchyFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCauchyFilterBasisFromEventFlow (realCauchyFilterBasisToEventFlow x) = some x
    exact RealCauchyFilterBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealCauchyFilterBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realCauchyFilterBasisFieldFaithful :
    FieldFaithful RealCauchyFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCauchyFilterBasisFields
  field_faithful := RealCauchyFilterBasisTasteGate_single_carrier_alignment_fields_faithful

instance realCauchyFilterBasisNontrivial : Nontrivial RealCauchyFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCauchyFilterBasisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCauchyFilterBasisUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RealCauchyFilterBasisTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RealCauchyFilterBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyFilterBasisChapterTasteGate

theorem RealCauchyFilterBasisTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealCauchyFilterBasisUp) ∧
      Nonempty (FieldFaithful RealCauchyFilterBasisUp) ∧
        Nonempty (Nontrivial RealCauchyFilterBasisUp) ∧
          (∀ h : BHist,
            realCauchyFilterBasisDecodeBHist (realCauchyFilterBasisEncodeBHist h) = h) ∧
            (∀ x : RealCauchyFilterBasisUp,
              realCauchyFilterBasisFromEventFlow (realCauchyFilterBasisToEventFlow x) =
                some x) ∧
              (∀ x y : RealCauchyFilterBasisUp,
                realCauchyFilterBasisToEventFlow x =
                    realCauchyFilterBasisToEventFlow y →
                  x = y) ∧
                realCauchyFilterBasisEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨realCauchyFilterBasisChapterTasteGate⟩,
      ⟨realCauchyFilterBasisFieldFaithful⟩,
      ⟨realCauchyFilterBasisNontrivial⟩,
      RealCauchyFilterBasisTasteGate_single_carrier_alignment_decode_encode,
      RealCauchyFilterBasisTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealCauchyFilterBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealCauchyFilterBasisUp
