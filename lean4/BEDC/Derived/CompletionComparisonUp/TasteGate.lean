import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionComparisonUp : Type where
  | mk (M F T R S U H C P N : BHist) : CompletionComparisonUp
  deriving DecidableEq

def completionComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionComparisonEncodeBHist h

def completionComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionComparisonDecodeBHist tail)

private theorem CompletionComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      completionComparisonDecodeBHist (completionComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionComparisonFields : CompletionComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionComparisonUp.mk M F T R S U H C P N => [M, F, T, R, S, U, H, C, P, N]

def completionComparisonToEventFlow : CompletionComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completionComparisonFields x).map completionComparisonEncodeBHist

private def completionComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completionComparisonEventAtDefault index rest

def completionComparisonFromEventFlow : EventFlow → Option CompletionComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CompletionComparisonUp.mk
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 0 ef))
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 1 ef))
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 2 ef))
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 3 ef))
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 4 ef))
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 5 ef))
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 6 ef))
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 7 ef))
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 8 ef))
          (completionComparisonDecodeBHist (completionComparisonEventAtDefault 9 ef)))

private theorem CompletionComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionComparisonUp,
      completionComparisonFromEventFlow (completionComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F T R S U H C P N =>
      change
        some
          (CompletionComparisonUp.mk
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist M))
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist F))
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist T))
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist R))
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist S))
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist U))
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist H))
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist C))
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist P))
            (completionComparisonDecodeBHist (completionComparisonEncodeBHist N))) =
          some (CompletionComparisonUp.mk M F T R S U H C P N)
      rw [CompletionComparisonTasteGate_single_carrier_alignment_decode M,
        CompletionComparisonTasteGate_single_carrier_alignment_decode F,
        CompletionComparisonTasteGate_single_carrier_alignment_decode T,
        CompletionComparisonTasteGate_single_carrier_alignment_decode R,
        CompletionComparisonTasteGate_single_carrier_alignment_decode S,
        CompletionComparisonTasteGate_single_carrier_alignment_decode U,
        CompletionComparisonTasteGate_single_carrier_alignment_decode H,
        CompletionComparisonTasteGate_single_carrier_alignment_decode C,
        CompletionComparisonTasteGate_single_carrier_alignment_decode P,
        CompletionComparisonTasteGate_single_carrier_alignment_decode N]

private theorem CompletionComparisonToEventFlow_injective {x y : CompletionComparisonUp} :
    completionComparisonToEventFlow x = completionComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionComparisonFromEventFlow (completionComparisonToEventFlow x) =
        completionComparisonFromEventFlow (completionComparisonToEventFlow y) :=
    congrArg completionComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompletionComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompletionComparisonTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompletionComparisonTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompletionComparisonUp,
      completionComparisonFields x = completionComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 F1 T1 R1 S1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 F2 T2 R2 S2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance completionComparisonBHistCarrier : BHistCarrier CompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionComparisonToEventFlow
  fromEventFlow := completionComparisonFromEventFlow

instance completionComparisonChapterTasteGate : ChapterTasteGate CompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionComparisonFromEventFlow (completionComparisonToEventFlow x) = some x
    exact CompletionComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionComparisonToEventFlow_injective heq)

instance completionComparisonFieldFaithful : FieldFaithful CompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionComparisonFields
  field_faithful := CompletionComparisonTasteGate_single_carrier_alignment_fields

instance completionComparisonNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompletionComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompletionComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompletionComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionComparisonChapterTasteGate

theorem CompletionComparisonTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompletionComparisonUp) ∧
      Nonempty (FieldFaithful CompletionComparisonUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CompletionComparisonUp) ∧
      (∀ h : BHist, completionComparisonDecodeBHist (completionComparisonEncodeBHist h) = h) ∧
      (∀ x : CompletionComparisonUp,
        completionComparisonFromEventFlow (completionComparisonToEventFlow x) = some x) ∧
      (∀ x y : CompletionComparisonUp,
        completionComparisonToEventFlow x = completionComparisonToEventFlow y → x = y) ∧
      completionComparisonEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨completionComparisonChapterTasteGate⟩,
      ⟨completionComparisonFieldFaithful⟩,
      ⟨completionComparisonNontrivial⟩,
      CompletionComparisonTasteGate_single_carrier_alignment_decode,
      CompletionComparisonTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CompletionComparisonToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompletionComparisonUp
