import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalBracketingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalBracketingUp : Type where
  | mk (L U D S R E N H C P A : BHist) : RationalBracketingUp
  deriving DecidableEq

def rationalBracketingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalBracketingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalBracketingEncodeBHist h

def rationalBracketingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalBracketingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalBracketingDecodeBHist tail)

private theorem RationalBracketingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, rationalBracketingDecodeBHist (rationalBracketingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalBracketingFields : RationalBracketingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalBracketingUp.mk L U D S R E N H C P A => [L, U, D, S, R, E, N, H, C, P, A]

def rationalBracketingToEventFlow : RationalBracketingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalBracketingFields x).map rationalBracketingEncodeBHist

private def rationalBracketingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalBracketingEventAt index rest

def rationalBracketingFromEventFlow (ef : EventFlow) : Option RationalBracketingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RationalBracketingUp.mk
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 0 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 1 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 2 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 3 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 4 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 5 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 6 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 7 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 8 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 9 ef))
      (rationalBracketingDecodeBHist (rationalBracketingEventAt 10 ef)))

private theorem RationalBracketingTasteGate_single_carrier_alignment_round_trip
    (x : RationalBracketingUp) :
    rationalBracketingFromEventFlow (rationalBracketingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U D S R E N H C P A =>
      change
        some
          (RationalBracketingUp.mk
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist L))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist U))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist D))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist S))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist R))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist E))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist N))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist H))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist C))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist P))
            (rationalBracketingDecodeBHist (rationalBracketingEncodeBHist A))) =
          some (RationalBracketingUp.mk L U D S R E N H C P A)
      rw [RationalBracketingTasteGate_single_carrier_alignment_decode_encode L,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode U,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode D,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode S,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode R,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode E,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode N,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode H,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode C,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode P,
        RationalBracketingTasteGate_single_carrier_alignment_decode_encode A]

private theorem RationalBracketingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalBracketingUp} :
    rationalBracketingToEventFlow x = rationalBracketingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalBracketingFromEventFlow (rationalBracketingToEventFlow x) =
        rationalBracketingFromEventFlow (rationalBracketingToEventFlow y) :=
    congrArg rationalBracketingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalBracketingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalBracketingTasteGate_single_carrier_alignment_round_trip y)))

private theorem RationalBracketingTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RationalBracketingUp, rationalBracketingFields x = rationalBracketingFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ U₁ D₁ S₁ R₁ E₁ N₁ H₁ C₁ P₁ A₁ =>
      cases y with
      | mk L₂ U₂ D₂ S₂ R₂ E₂ N₂ H₂ C₂ P₂ A₂ =>
          cases hfields
          rfl

instance rationalBracketingBHistCarrier : BHistCarrier RationalBracketingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalBracketingToEventFlow
  fromEventFlow := rationalBracketingFromEventFlow

instance rationalBracketingChapterTasteGate : ChapterTasteGate RationalBracketingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rationalBracketingFromEventFlow (rationalBracketingToEventFlow x) = some x
    exact RationalBracketingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RationalBracketingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rationalBracketingFieldFaithful : FieldFaithful RationalBracketingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalBracketingFields
  field_faithful := RationalBracketingTasteGate_single_carrier_alignment_fields_faithful

instance rationalBracketingNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RationalBracketingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalBracketingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RationalBracketingUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RationalBracketingTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RationalBracketingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalBracketingChapterTasteGate

theorem RationalBracketingTasteGate_single_carrier_alignment :
    (∀ h : BHist, rationalBracketingDecodeBHist (rationalBracketingEncodeBHist h) = h) ∧
      (∀ x : RationalBracketingUp,
        rationalBracketingFromEventFlow (rationalBracketingToEventFlow x) = some x) ∧
        (∀ x y : RationalBracketingUp,
          rationalBracketingToEventFlow x = rationalBracketingToEventFlow y → x = y) ∧
          rationalBracketingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨RationalBracketingTasteGate_single_carrier_alignment_decode_encode,
      RationalBracketingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RationalBracketingTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RationalBracketingUp.TasteGate

namespace BEDC.Derived.RationalBracketingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem RationalBracketingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.rationalBracketingDecodeBHist (TasteGate.rationalBracketingEncodeBHist h) =
        h) ∧
      (∀ x : TasteGate.RationalBracketingUp,
        TasteGate.rationalBracketingFromEventFlow (TasteGate.rationalBracketingToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGate.RationalBracketingUp,
          TasteGate.rationalBracketingToEventFlow x =
              TasteGate.rationalBracketingToEventFlow y →
            x = y) ∧
          TasteGate.rationalBracketingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact TasteGate.RationalBracketingTasteGate_single_carrier_alignment

end BEDC.Derived.RationalBracketingUp
