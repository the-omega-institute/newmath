import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyStabilityUp : Type where
  | mk (A B M D R E H C P N : BHist) : CauchyStabilityUp
  deriving DecidableEq

def cauchyStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyStabilityEncodeBHist h

def cauchyStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyStabilityDecodeBHist tail)

private theorem CauchyStabilityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyStabilityFields : CauchyStabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyStabilityUp.mk A B M D R E H C P N => [A, B, M, D, R, E, H, C, P, N]

def cauchyStabilityToEventFlow : CauchyStabilityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyStabilityFields x).map cauchyStabilityEncodeBHist

private def cauchyStabilityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyStabilityEventAtDefault index rest

def cauchyStabilityFromEventFlow (ef : EventFlow) : Option CauchyStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyStabilityUp.mk
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 0 ef))
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 1 ef))
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 2 ef))
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 3 ef))
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 4 ef))
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 5 ef))
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 6 ef))
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 7 ef))
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 8 ef))
      (cauchyStabilityDecodeBHist (cauchyStabilityEventAtDefault 9 ef)))

private theorem CauchyStabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyStabilityUp,
      cauchyStabilityFromEventFlow (cauchyStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B M D R E H C P N =>
      change
        some
          (CauchyStabilityUp.mk
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist A))
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist B))
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist M))
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist D))
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist R))
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist E))
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist H))
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist C))
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist P))
            (cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist N))) =
          some (CauchyStabilityUp.mk A B M D R E H C P N)
      rw [CauchyStabilityTasteGate_single_carrier_alignment_decode A,
        CauchyStabilityTasteGate_single_carrier_alignment_decode B,
        CauchyStabilityTasteGate_single_carrier_alignment_decode M,
        CauchyStabilityTasteGate_single_carrier_alignment_decode D,
        CauchyStabilityTasteGate_single_carrier_alignment_decode R,
        CauchyStabilityTasteGate_single_carrier_alignment_decode E,
        CauchyStabilityTasteGate_single_carrier_alignment_decode H,
        CauchyStabilityTasteGate_single_carrier_alignment_decode C,
        CauchyStabilityTasteGate_single_carrier_alignment_decode P,
        CauchyStabilityTasteGate_single_carrier_alignment_decode N]

private theorem CauchyStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyStabilityUp} :
    cauchyStabilityToEventFlow x = cauchyStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyStabilityFromEventFlow (cauchyStabilityToEventFlow x) =
        cauchyStabilityFromEventFlow (cauchyStabilityToEventFlow y) :=
    congrArg cauchyStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyStabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyStabilityTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyStabilityTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyStabilityUp,
      cauchyStabilityFields x = cauchyStabilityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ M₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ M₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyStabilityBHistCarrier : BHistCarrier CauchyStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyStabilityToEventFlow
  fromEventFlow := cauchyStabilityFromEventFlow

instance cauchyStabilityChapterTasteGate : ChapterTasteGate CauchyStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyStabilityFromEventFlow (cauchyStabilityToEventFlow x) = some x
    exact CauchyStabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyStabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyStabilityFieldFaithful : FieldFaithful CauchyStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyStabilityFields
  field_faithful := CauchyStabilityTasteGate_single_carrier_alignment_fields

instance cauchyStabilityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyStabilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyStabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyStabilityChapterTasteGate

theorem CauchyStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyStabilityDecodeBHist (cauchyStabilityEncodeBHist h) = h) ∧
      (∀ x : CauchyStabilityUp,
        cauchyStabilityFromEventFlow (cauchyStabilityToEventFlow x) = some x) ∧
        (∀ x y : CauchyStabilityUp,
          cauchyStabilityToEventFlow x = cauchyStabilityToEventFlow y → x = y) ∧
          cauchyStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchyStabilityTasteGate_single_carrier_alignment_decode,
      CauchyStabilityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyStabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyStabilityUp
