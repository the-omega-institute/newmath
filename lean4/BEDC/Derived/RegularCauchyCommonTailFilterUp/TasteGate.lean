import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCommonTailFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCommonTailFilterUp : Type where
  | mk (X Sigma T R D Q E H C P N : BHist) : RegularCauchyCommonTailFilterUp
  deriving DecidableEq

def regularCauchyCommonTailFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCommonTailFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCommonTailFilterEncodeBHist h

def regularCauchyCommonTailFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCommonTailFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCommonTailFilterDecodeBHist tail)

private theorem RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyCommonTailFilterFields : RegularCauchyCommonTailFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCommonTailFilterUp.mk X Sigma T R D Q E H C P N => [X, Sigma, T, R, D, Q, E, H, C, P, N]

def regularCauchyCommonTailFilterToEventFlow : RegularCauchyCommonTailFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyCommonTailFilterFields x).map regularCauchyCommonTailFilterEncodeBHist

private def regularCauchyCommonTailFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCommonTailFilterEventAtDefault index rest

def regularCauchyCommonTailFilterFromEventFlow (ef : EventFlow) : Option RegularCauchyCommonTailFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (RegularCauchyCommonTailFilterUp.mk
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 0 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 1 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 2 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 3 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 4 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 5 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 6 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 7 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 8 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 9 ef))
      (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEventAtDefault 10 ef)))

private theorem RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCommonTailFilterUp, regularCauchyCommonTailFilterFromEventFlow (regularCauchyCommonTailFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Sigma T R D Q E H C P N =>
      change
        some (RegularCauchyCommonTailFilterUp.mk
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist X))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist Sigma))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist T))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist R))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist D))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist Q))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist E))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist H))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist C))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist P))
          (regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist N))
          ) = some (RegularCauchyCommonTailFilterUp.mk X Sigma T R D Q E H C P N)
      rw [RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode X, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode Sigma, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode T, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode R, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode D, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode Q, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode E, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode H, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode C, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode P, RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCommonTailFilterUp} :
    regularCauchyCommonTailFilterToEventFlow x = regularCauchyCommonTailFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCommonTailFilterFromEventFlow (regularCauchyCommonTailFilterToEventFlow x) =
        regularCauchyCommonTailFilterFromEventFlow (regularCauchyCommonTailFilterToEventFlow y) :=
    congrArg regularCauchyCommonTailFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyCommonTailFilterUp, regularCauchyCommonTailFilterFields x = regularCauchyCommonTailFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Sigma₁ T₁ R₁ D₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Sigma₂ T₂ R₂ D₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyCommonTailFilterBHistCarrier : BHistCarrier RegularCauchyCommonTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCommonTailFilterToEventFlow
  fromEventFlow := regularCauchyCommonTailFilterFromEventFlow

instance regularCauchyCommonTailFilterChapterTasteGate : ChapterTasteGate RegularCauchyCommonTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyCommonTailFilterFromEventFlow (regularCauchyCommonTailFilterToEventFlow x) = some x
    exact RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyCommonTailFilterFieldFaithful : FieldFaithful RegularCauchyCommonTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCommonTailFilterFields
  field_faithful := RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyCommonTailFilterNontrivial : Nontrivial RegularCauchyCommonTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCommonTailFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyCommonTailFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyCommonTailFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCommonTailFilterChapterTasteGate

theorem RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyCommonTailFilterDecodeBHist (regularCauchyCommonTailFilterEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCommonTailFilterUp, regularCauchyCommonTailFilterFromEventFlow (regularCauchyCommonTailFilterToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyCommonTailFilterUp,
          regularCauchyCommonTailFilterToEventFlow x = regularCauchyCommonTailFilterToEventFlow y → x = y) ∧
          regularCauchyCommonTailFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RegularCauchyCommonTailFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyCommonTailFilterUp
