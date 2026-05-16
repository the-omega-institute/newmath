import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWindowRealSeparationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWindowRealSeparationUp : Type where
  | mk (W D S R H C P N : BHist) : FiniteWindowRealSeparationUp
  deriving DecidableEq

def finiteWindowRealSeparationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowRealSeparationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowRealSeparationEncodeBHist h

def finiteWindowRealSeparationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowRealSeparationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowRealSeparationDecodeBHist tail)

private theorem FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteWindowRealSeparationToEventFlow :
    FiniteWindowRealSeparationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowRealSeparationUp.mk W D S R H C P N =>
      [[BMark.b0],
        finiteWindowRealSeparationEncodeBHist W,
        [BMark.b1, BMark.b0],
        finiteWindowRealSeparationEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSeparationEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSeparationEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSeparationEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSeparationEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSeparationEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteWindowRealSeparationEncodeBHist N]

private def finiteWindowRealSeparationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteWindowRealSeparationEventAtDefault index rest

def finiteWindowRealSeparationFromEventFlow
    (ef : EventFlow) : Option FiniteWindowRealSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteWindowRealSeparationUp.mk
      (finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEventAtDefault 1 ef))
      (finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEventAtDefault 3 ef))
      (finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEventAtDefault 5 ef))
      (finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEventAtDefault 7 ef))
      (finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEventAtDefault 9 ef))
      (finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEventAtDefault 11 ef))
      (finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEventAtDefault 13 ef))
      (finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEventAtDefault 15 ef)))

private theorem FiniteWindowRealSeparationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteWindowRealSeparationUp,
      finiteWindowRealSeparationFromEventFlow
        (finiteWindowRealSeparationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W D S R H C P N =>
      change
        some
          (FiniteWindowRealSeparationUp.mk
            (finiteWindowRealSeparationDecodeBHist
              (finiteWindowRealSeparationEncodeBHist W))
            (finiteWindowRealSeparationDecodeBHist
              (finiteWindowRealSeparationEncodeBHist D))
            (finiteWindowRealSeparationDecodeBHist
              (finiteWindowRealSeparationEncodeBHist S))
            (finiteWindowRealSeparationDecodeBHist
              (finiteWindowRealSeparationEncodeBHist R))
            (finiteWindowRealSeparationDecodeBHist
              (finiteWindowRealSeparationEncodeBHist H))
            (finiteWindowRealSeparationDecodeBHist
              (finiteWindowRealSeparationEncodeBHist C))
            (finiteWindowRealSeparationDecodeBHist
              (finiteWindowRealSeparationEncodeBHist P))
            (finiteWindowRealSeparationDecodeBHist
              (finiteWindowRealSeparationEncodeBHist N))) =
          some (FiniteWindowRealSeparationUp.mk W D S R H C P N)
      rw [FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode W,
        FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode D,
        FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode S,
        FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode R,
        FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode H,
        FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode C,
        FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode P,
        FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode N]

private theorem FiniteWindowRealSeparationTasteGate_single_carrier_alignment_injective
    {x y : FiniteWindowRealSeparationUp} :
    finiteWindowRealSeparationToEventFlow x =
      finiteWindowRealSeparationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowRealSeparationFromEventFlow
          (finiteWindowRealSeparationToEventFlow x) =
        finiteWindowRealSeparationFromEventFlow
          (finiteWindowRealSeparationToEventFlow y) :=
    congrArg finiteWindowRealSeparationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteWindowRealSeparationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteWindowRealSeparationTasteGate_single_carrier_alignment_round_trip y)))

private def finiteWindowRealSeparationFields :
    FiniteWindowRealSeparationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowRealSeparationUp.mk W D S R H C P N => [W, D, S, R, H, C, P, N]

private theorem FiniteWindowRealSeparationTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteWindowRealSeparationUp,
      finiteWindowRealSeparationFields x = finiteWindowRealSeparationFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 D1 S1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 D2 S2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteWindowRealSeparationBHistCarrier :
    BHistCarrier FiniteWindowRealSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowRealSeparationToEventFlow
  fromEventFlow := finiteWindowRealSeparationFromEventFlow

instance finiteWindowRealSeparationChapterTasteGate :
    ChapterTasteGate FiniteWindowRealSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteWindowRealSeparationFromEventFlow
        (finiteWindowRealSeparationToEventFlow x) = some x
    exact FiniteWindowRealSeparationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteWindowRealSeparationTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate FiniteWindowRealSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteWindowRealSeparationChapterTasteGate

instance finiteWindowRealSeparationFieldFaithful :
    FieldFaithful FiniteWindowRealSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteWindowRealSeparationFields
  field_faithful := FiniteWindowRealSeparationTasteGate_single_carrier_alignment_fields

instance finiteWindowRealSeparationNontrivial :
    Nontrivial FiniteWindowRealSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteWindowRealSeparationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteWindowRealSeparationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteWindowRealSeparationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteWindowRealSeparationDecodeBHist
        (finiteWindowRealSeparationEncodeBHist h) = h) ∧
      (∀ x : FiniteWindowRealSeparationUp,
        finiteWindowRealSeparationFromEventFlow
          (finiteWindowRealSeparationToEventFlow x) = some x) ∧
        (∀ x y : FiniteWindowRealSeparationUp,
          finiteWindowRealSeparationToEventFlow x =
            finiteWindowRealSeparationToEventFlow y → x = y) ∧
          finiteWindowRealSeparationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FiniteWindowRealSeparationTasteGate_single_carrier_alignment_decode,
      FiniteWindowRealSeparationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteWindowRealSeparationTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.FiniteWindowRealSeparationUp
