import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionCriterionUp : Type where
  | mk (S R D M Q E H C P N : BHist) : CauchyCompletionCriterionUp
  deriving DecidableEq

def cauchyCompletionCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionCriterionEncodeBHist h

def cauchyCompletionCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionCriterionDecodeBHist tail)

private theorem CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionCriterionFields : CauchyCompletionCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionCriterionUp.mk S R D M Q E H C P N => [S, R, D, M, Q, E, H, C, P, N]

def cauchyCompletionCriterionToEventFlow : CauchyCompletionCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyCompletionCriterionFields x).map cauchyCompletionCriterionEncodeBHist

private def cauchyCompletionCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionCriterionEventAt index rest

def cauchyCompletionCriterionFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionCriterionUp.mk
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 0 ef))
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 1 ef))
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 2 ef))
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 3 ef))
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 4 ef))
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 5 ef))
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 6 ef))
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 7 ef))
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 8 ef))
      (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEventAt 9 ef)))

private theorem CauchyCompletionCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionCriterionUp,
      cauchyCompletionCriterionFromEventFlow (cauchyCompletionCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D M Q E H C P N =>
      change
        some
          (CauchyCompletionCriterionUp.mk
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist S))
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist R))
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist D))
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist M))
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist Q))
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist E))
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist H))
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist C))
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist P))
            (cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist N))) =
          some (CauchyCompletionCriterionUp.mk S R D M Q E H C P N)
      rw [CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode S,
        CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode R,
        CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode D,
        CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode M,
        CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode Q,
        CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionCriterionTasteGate_single_carrier_alignment_injective
    {x y : CauchyCompletionCriterionUp} :
    cauchyCompletionCriterionToEventFlow x = cauchyCompletionCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionCriterionFromEventFlow (cauchyCompletionCriterionToEventFlow x) =
        cauchyCompletionCriterionFromEventFlow (cauchyCompletionCriterionToEventFlow y) :=
    congrArg cauchyCompletionCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletionCriterionTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyCompletionCriterionUp,
      cauchyCompletionCriterionFields x = cauchyCompletionCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 D1 M1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 D2 M2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyCompletionCriterionBHistCarrier : BHistCarrier CauchyCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionCriterionToEventFlow
  fromEventFlow := cauchyCompletionCriterionFromEventFlow

instance cauchyCompletionCriterionChapterTasteGate :
    ChapterTasteGate CauchyCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionCriterionFromEventFlow (cauchyCompletionCriterionToEventFlow x) = some x
    exact CauchyCompletionCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionCriterionTasteGate_single_carrier_alignment_injective heq)

instance cauchyCompletionCriterionFieldFaithful : FieldFaithful CauchyCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionCriterionFields
  field_faithful := CauchyCompletionCriterionTasteGate_single_carrier_alignment_fields

instance cauchyCompletionCriterionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyCompletionCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyCompletionCriterionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletionCriterionUp) ∧
      Nonempty (FieldFaithful CauchyCompletionCriterionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyCompletionCriterionUp) ∧
      (∀ h : BHist,
        cauchyCompletionCriterionDecodeBHist (cauchyCompletionCriterionEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionCriterionUp,
        cauchyCompletionCriterionFromEventFlow (cauchyCompletionCriterionToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyCompletionCriterionUp,
        cauchyCompletionCriterionToEventFlow x = cauchyCompletionCriterionToEventFlow y →
          x = y) ∧
      cauchyCompletionCriterionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro cauchyCompletionCriterionChapterTasteGate,
      Nonempty.intro cauchyCompletionCriterionFieldFaithful,
      Nonempty.intro cauchyCompletionCriterionNontrivial,
      CauchyCompletionCriterionTasteGate_single_carrier_alignment_decode,
      CauchyCompletionCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyCompletionCriterionTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionCriterionUp
