import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyBallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyBallUp : Type where
  | mk (X C R W D Q S H T P N : BHist) : RegularCauchyBallUp
  deriving DecidableEq

def regularCauchyBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyBallEncodeBHist h

def regularCauchyBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyBallDecodeBHist tail)

private theorem RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyBallFields : RegularCauchyBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyBallUp.mk X C R W D Q S H T P N => [X, C, R, W, D, Q, S, H, T, P, N]

def regularCauchyBallToEventFlow : RegularCauchyBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyBallFields x).map regularCauchyBallEncodeBHist

private def regularCauchyBallRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => regularCauchyBallRawAt index rest

def regularCauchyBallFromEventFlow (flow : EventFlow) : Option RegularCauchyBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyBallUp.mk
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 0 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 1 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 2 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 3 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 4 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 5 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 6 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 7 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 8 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 9 flow))
      (regularCauchyBallDecodeBHist (regularCauchyBallRawAt 10 flow)))

private theorem RegularCauchyBallUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyBallUp,
      regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X C R W D Q S H T P N =>
      change
        some
          (RegularCauchyBallUp.mk
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist X))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist C))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist R))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist W))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist D))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist Q))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist S))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist H))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist T))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist P))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist N))) =
          some (RegularCauchyBallUp.mk X C R W D Q S H T P N)
      rw [RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode X,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode T,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyBallUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyBallUp} :
    regularCauchyBallToEventFlow x = regularCauchyBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow x) =
        regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow y) :=
    congrArg regularCauchyBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyBallUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyBallUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyBallUpTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyBallUp,
      regularCauchyBallFields x = regularCauchyBallFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ C₁ R₁ W₁ D₁ Q₁ S₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk X₂ C₂ R₂ W₂ D₂ Q₂ S₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyBallBHistCarrier : BHistCarrier RegularCauchyBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyBallToEventFlow
  fromEventFlow := regularCauchyBallFromEventFlow

instance regularCauchyBallChapterTasteGate : ChapterTasteGate RegularCauchyBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow x) = some x
    exact RegularCauchyBallUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyBallUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyBallFieldFaithful : FieldFaithful RegularCauchyBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyBallFields
  field_faithful := RegularCauchyBallUpTasteGate_single_carrier_alignment_field_faithful

instance regularCauchyBallNontrivial : Nontrivial RegularCauchyBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyBallUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyBallChapterTasteGate

theorem RegularCauchyBallUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyBallUp) ∧
      Nonempty (FieldFaithful RegularCauchyBallUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyBallUp) ∧
          (∀ h : BHist, regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyBallUp,
              regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow x) = some x) ∧
              (∀ x y : RegularCauchyBallUp,
                regularCauchyBallToEventFlow x = regularCauchyBallToEventFlow y → x = y) ∧
                regularCauchyBallEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨regularCauchyBallChapterTasteGate⟩,
      ⟨⟨regularCauchyBallFieldFaithful⟩,
        ⟨⟨regularCauchyBallNontrivial⟩,
          ⟨RegularCauchyBallUpTasteGate_single_carrier_alignment_decode_encode,
            ⟨RegularCauchyBallUpTasteGate_single_carrier_alignment_round_trip,
              ⟨(fun _ _ heq =>
                  RegularCauchyBallUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
                rfl⟩⟩⟩⟩⟩⟩

end BEDC.Derived.RegularCauchyBallUp
