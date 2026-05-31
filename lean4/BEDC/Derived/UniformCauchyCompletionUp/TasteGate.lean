import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyCompletionUp : Type where
  | mk (F S R D E H C P N : BHist) : UniformCauchyCompletionUp
  deriving DecidableEq

def uniformCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyCompletionEncodeBHist h

def uniformCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyCompletionDecodeBHist tail)

private theorem UniformCauchyCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCauchyCompletionFields : UniformCauchyCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyCompletionUp.mk F S R D E H C P N => [F, S, R, D, E, H, C, P, N]

def uniformCauchyCompletionToEventFlow : UniformCauchyCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformCauchyCompletionFields x).map uniformCauchyCompletionEncodeBHist

private def uniformCauchyCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformCauchyCompletionEventAtDefault index rest

def uniformCauchyCompletionFromEventFlow
    (ef : EventFlow) : Option UniformCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCauchyCompletionUp.mk
      (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEventAtDefault 0 ef))
      (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEventAtDefault 1 ef))
      (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEventAtDefault 2 ef))
      (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEventAtDefault 3 ef))
      (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEventAtDefault 4 ef))
      (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEventAtDefault 5 ef))
      (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEventAtDefault 6 ef))
      (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEventAtDefault 7 ef))
      (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEventAtDefault 8 ef)))

private theorem UniformCauchyCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCauchyCompletionUp,
      uniformCauchyCompletionFromEventFlow
        (uniformCauchyCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S R D E H C P N =>
      change
        some
            (UniformCauchyCompletionUp.mk
              (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist F))
              (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist S))
              (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist R))
              (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist D))
              (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist E))
              (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist H))
              (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist C))
              (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist P))
              (uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist N))) =
          some (UniformCauchyCompletionUp.mk F S R D E H C P N)
      rw [UniformCauchyCompletionTasteGate_single_carrier_alignment_decode F,
        UniformCauchyCompletionTasteGate_single_carrier_alignment_decode S,
        UniformCauchyCompletionTasteGate_single_carrier_alignment_decode R,
        UniformCauchyCompletionTasteGate_single_carrier_alignment_decode D,
        UniformCauchyCompletionTasteGate_single_carrier_alignment_decode E,
        UniformCauchyCompletionTasteGate_single_carrier_alignment_decode H,
        UniformCauchyCompletionTasteGate_single_carrier_alignment_decode C,
        UniformCauchyCompletionTasteGate_single_carrier_alignment_decode P,
        UniformCauchyCompletionTasteGate_single_carrier_alignment_decode N]

private theorem UniformCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCauchyCompletionUp} :
    uniformCauchyCompletionToEventFlow x = uniformCauchyCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchyCompletionFromEventFlow (uniformCauchyCompletionToEventFlow x) =
        uniformCauchyCompletionFromEventFlow (uniformCauchyCompletionToEventFlow y) :=
    congrArg uniformCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformCauchyCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformCauchyCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformCauchyCompletionTasteGate_single_carrier_alignment_fields :
    ∀ x y : UniformCauchyCompletionUp,
      uniformCauchyCompletionFields x = uniformCauchyCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 S2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformCauchyCompletionBHistCarrier :
    BHistCarrier UniformCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchyCompletionToEventFlow
  fromEventFlow := uniformCauchyCompletionFromEventFlow

instance uniformCauchyCompletionChapterTasteGate :
    ChapterTasteGate UniformCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCauchyCompletionFromEventFlow
        (uniformCauchyCompletionToEventFlow x) = some x
    exact UniformCauchyCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformCauchyCompletionFieldFaithful :
    FieldFaithful UniformCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformCauchyCompletionFields
  field_faithful := UniformCauchyCompletionTasteGate_single_carrier_alignment_fields

instance uniformCauchyCompletionNontrivial : Nontrivial UniformCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCauchyCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCauchyCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCauchyCompletionChapterTasteGate

theorem UniformCauchyCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformCauchyCompletionDecodeBHist (uniformCauchyCompletionEncodeBHist h) = h) ∧
      (∀ x : UniformCauchyCompletionUp,
        uniformCauchyCompletionFromEventFlow
          (uniformCauchyCompletionToEventFlow x) = some x) ∧
        (∀ x y : UniformCauchyCompletionUp,
          uniformCauchyCompletionToEventFlow x =
            uniformCauchyCompletionToEventFlow y → x = y) ∧
          uniformCauchyCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨UniformCauchyCompletionTasteGate_single_carrier_alignment_decode,
      UniformCauchyCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformCauchyCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformCauchyCompletionUp
