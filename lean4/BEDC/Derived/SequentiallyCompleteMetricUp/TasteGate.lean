import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentiallyCompleteMetricUp : Type where
  | mk (X S M L D H C P N : BHist) : SequentiallyCompleteMetricUp
  deriving DecidableEq

def sequentiallyCompleteMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentiallyCompleteMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentiallyCompleteMetricEncodeBHist h

def sequentiallyCompleteMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentiallyCompleteMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentiallyCompleteMetricDecodeBHist tail)

private theorem SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sequentiallyCompleteMetricFields : SequentiallyCompleteMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentiallyCompleteMetricUp.mk X S M L D H C P N => [X, S, M, L, D, H, C, P, N]

def sequentiallyCompleteMetricToEventFlow : SequentiallyCompleteMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sequentiallyCompleteMetricFields x).map sequentiallyCompleteMetricEncodeBHist

private def sequentiallyCompleteMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sequentiallyCompleteMetricEventAtDefault index rest

def sequentiallyCompleteMetricFromEventFlow
    (ef : EventFlow) : Option SequentiallyCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SequentiallyCompleteMetricUp.mk
      (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEventAtDefault 0 ef))
      (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEventAtDefault 1 ef))
      (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEventAtDefault 2 ef))
      (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEventAtDefault 3 ef))
      (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEventAtDefault 4 ef))
      (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEventAtDefault 5 ef))
      (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEventAtDefault 6 ef))
      (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEventAtDefault 7 ef))
      (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEventAtDefault 8 ef)))

private theorem SequentiallyCompleteMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SequentiallyCompleteMetricUp,
      sequentiallyCompleteMetricFromEventFlow (sequentiallyCompleteMetricToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X S M L D H C P N =>
      change
        some
          (SequentiallyCompleteMetricUp.mk
            (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist X))
            (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist S))
            (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist M))
            (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist L))
            (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist D))
            (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist H))
            (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist C))
            (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist P))
            (sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist N))) =
          some (SequentiallyCompleteMetricUp.mk X S M L D H C P N)
      rw [SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode X,
        SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode S,
        SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode M,
        SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode L,
        SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode D,
        SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode H,
        SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode C,
        SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode P,
        SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode N]

private theorem SequentiallyCompleteMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentiallyCompleteMetricUp} :
    sequentiallyCompleteMetricToEventFlow x = sequentiallyCompleteMetricToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentiallyCompleteMetricFromEventFlow (sequentiallyCompleteMetricToEventFlow x) =
        sequentiallyCompleteMetricFromEventFlow (sequentiallyCompleteMetricToEventFlow y) :=
    congrArg sequentiallyCompleteMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SequentiallyCompleteMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SequentiallyCompleteMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem SequentiallyCompleteMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : SequentiallyCompleteMetricUp,
      sequentiallyCompleteMetricFields x = sequentiallyCompleteMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ S₁ M₁ L₁ D₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ S₂ M₂ L₂ D₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance sequentiallyCompleteMetricBHistCarrier :
    BHistCarrier SequentiallyCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentiallyCompleteMetricToEventFlow
  fromEventFlow := sequentiallyCompleteMetricFromEventFlow

instance sequentiallyCompleteMetricChapterTasteGate :
    ChapterTasteGate SequentiallyCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sequentiallyCompleteMetricFromEventFlow (sequentiallyCompleteMetricToEventFlow x) =
        some x
    exact SequentiallyCompleteMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SequentiallyCompleteMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sequentiallyCompleteMetricFieldFaithful :
    FieldFaithful SequentiallyCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sequentiallyCompleteMetricFields
  field_faithful := SequentiallyCompleteMetricTasteGate_single_carrier_alignment_fields

instance sequentiallyCompleteMetricNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SequentiallyCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SequentiallyCompleteMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SequentiallyCompleteMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SequentiallyCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentiallyCompleteMetricChapterTasteGate

theorem SequentiallyCompleteMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sequentiallyCompleteMetricDecodeBHist (sequentiallyCompleteMetricEncodeBHist h) =
        h) ∧
      (∀ x : SequentiallyCompleteMetricUp,
        sequentiallyCompleteMetricFromEventFlow (sequentiallyCompleteMetricToEventFlow x) =
          some x) ∧
        (∀ x y : SequentiallyCompleteMetricUp,
          sequentiallyCompleteMetricToEventFlow x = sequentiallyCompleteMetricToEventFlow y ->
            x = y) ∧
          sequentiallyCompleteMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SequentiallyCompleteMetricTasteGate_single_carrier_alignment_decode,
      SequentiallyCompleteMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SequentiallyCompleteMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
