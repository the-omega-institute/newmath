import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyEntourageFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyEntourageFilterUp : Type where
  | mk (U B S R D E H C P N : BHist) : CauchyEntourageFilterUp
  deriving DecidableEq

def cauchyEntourageFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyEntourageFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyEntourageFilterEncodeBHist h

def cauchyEntourageFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyEntourageFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyEntourageFilterDecodeBHist tail)

private theorem CauchyEntourageFilterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyEntourageFilterFields : CauchyEntourageFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyEntourageFilterUp.mk U B S R D E H C P N => [U, B, S, R, D, E, H, C, P, N]

def cauchyEntourageFilterToEventFlow : CauchyEntourageFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyEntourageFilterFields x).map cauchyEntourageFilterEncodeBHist

private def cauchyEntourageFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyEntourageFilterEventAtDefault index rest

def cauchyEntourageFilterFromEventFlow (ef : EventFlow) : Option CauchyEntourageFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyEntourageFilterUp.mk
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 0 ef))
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 1 ef))
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 2 ef))
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 3 ef))
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 4 ef))
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 5 ef))
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 6 ef))
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 7 ef))
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 8 ef))
      (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEventAtDefault 9 ef)))

private theorem CauchyEntourageFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyEntourageFilterUp,
      cauchyEntourageFilterFromEventFlow (cauchyEntourageFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U B S R D E H C P N =>
      change
        some
            (CauchyEntourageFilterUp.mk
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist U))
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist B))
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist S))
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist R))
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist D))
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist E))
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist H))
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist C))
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist P))
              (cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist N))) =
          some (CauchyEntourageFilterUp.mk U B S R D E H C P N)
      rw [CauchyEntourageFilterTasteGate_single_carrier_alignment_decode U,
        CauchyEntourageFilterTasteGate_single_carrier_alignment_decode B,
        CauchyEntourageFilterTasteGate_single_carrier_alignment_decode S,
        CauchyEntourageFilterTasteGate_single_carrier_alignment_decode R,
        CauchyEntourageFilterTasteGate_single_carrier_alignment_decode D,
        CauchyEntourageFilterTasteGate_single_carrier_alignment_decode E,
        CauchyEntourageFilterTasteGate_single_carrier_alignment_decode H,
        CauchyEntourageFilterTasteGate_single_carrier_alignment_decode C,
        CauchyEntourageFilterTasteGate_single_carrier_alignment_decode P,
        CauchyEntourageFilterTasteGate_single_carrier_alignment_decode N]

private theorem CauchyEntourageFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyEntourageFilterUp} :
    cauchyEntourageFilterToEventFlow x = cauchyEntourageFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyEntourageFilterFromEventFlow (cauchyEntourageFilterToEventFlow x) =
        cauchyEntourageFilterFromEventFlow (cauchyEntourageFilterToEventFlow y) :=
    congrArg cauchyEntourageFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyEntourageFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyEntourageFilterTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyEntourageFilterTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyEntourageFilterUp,
      cauchyEntourageFilterFields x = cauchyEntourageFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 B1 S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 B2 S2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyEntourageFilterBHistCarrier : BHistCarrier CauchyEntourageFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyEntourageFilterToEventFlow
  fromEventFlow := cauchyEntourageFilterFromEventFlow

instance cauchyEntourageFilterChapterTasteGate : ChapterTasteGate CauchyEntourageFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyEntourageFilterFromEventFlow (cauchyEntourageFilterToEventFlow x) = some x
    exact CauchyEntourageFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyEntourageFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyEntourageFilterFieldFaithful : FieldFaithful CauchyEntourageFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyEntourageFilterFields
  field_faithful := CauchyEntourageFilterTasteGate_single_carrier_alignment_fields

instance cauchyEntourageFilterNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyEntourageFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyEntourageFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyEntourageFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyEntourageFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyEntourageFilterChapterTasteGate

theorem CauchyEntourageFilterTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyEntourageFilterUp) ∧
      Nonempty (FieldFaithful CauchyEntourageFilterUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyEntourageFilterUp) ∧
          (∀ h : BHist,
            cauchyEntourageFilterDecodeBHist (cauchyEntourageFilterEncodeBHist h) = h) ∧
            (∀ x : CauchyEntourageFilterUp,
              cauchyEntourageFilterFromEventFlow
                  (cauchyEntourageFilterToEventFlow x) =
                some x) ∧
              (∀ x y : CauchyEntourageFilterUp,
                cauchyEntourageFilterToEventFlow x = cauchyEntourageFilterToEventFlow y →
                  x = y) ∧
                cauchyEntourageFilterEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyEntourageFilterChapterTasteGate⟩,
      ⟨cauchyEntourageFilterFieldFaithful⟩,
      ⟨cauchyEntourageFilterNontrivial⟩,
      CauchyEntourageFilterTasteGate_single_carrier_alignment_decode,
      CauchyEntourageFilterTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyEntourageFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyEntourageFilterUp
