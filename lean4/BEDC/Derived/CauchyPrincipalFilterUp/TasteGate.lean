import BEDC.Derived.CauchyPrincipalFilterUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyPrincipalFilterUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyPrincipalFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyPrincipalFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyPrincipalFilterEncodeBHist h

def cauchyPrincipalFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyPrincipalFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyPrincipalFilterDecodeBHist tail)

private theorem CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyPrincipalFilterFields : CauchyPrincipalFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyPrincipalFilterUp.mk A G F U B H K P N => [A, G, F, U, B, H, K, P, N]

def cauchyPrincipalFilterToEventFlow : CauchyPrincipalFilterUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyPrincipalFilterFields x).map cauchyPrincipalFilterEncodeBHist

private def cauchyPrincipalFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyPrincipalFilterEventAtDefault index rest

def cauchyPrincipalFilterFromEventFlow (ef : EventFlow) : Option CauchyPrincipalFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyPrincipalFilterUp.mk
      (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEventAtDefault 0 ef))
      (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEventAtDefault 1 ef))
      (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEventAtDefault 2 ef))
      (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEventAtDefault 3 ef))
      (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEventAtDefault 4 ef))
      (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEventAtDefault 5 ef))
      (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEventAtDefault 6 ef))
      (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEventAtDefault 7 ef))
      (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEventAtDefault 8 ef)))

private theorem CauchyPrincipalFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyPrincipalFilterUp,
      cauchyPrincipalFilterFromEventFlow (cauchyPrincipalFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A G F U B H K P N =>
      change
        some
          (CauchyPrincipalFilterUp.mk
            (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist A))
            (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist G))
            (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist F))
            (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist U))
            (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist B))
            (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist H))
            (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist K))
            (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist P))
            (cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist N))) =
          some (CauchyPrincipalFilterUp.mk A G F U B H K P N)
      rw [CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode A,
        CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode G,
        CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode F,
        CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode U,
        CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode B,
        CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode H,
        CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode K,
        CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode P,
        CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyPrincipalFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyPrincipalFilterUp} :
    cauchyPrincipalFilterToEventFlow x = cauchyPrincipalFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyPrincipalFilterFromEventFlow (cauchyPrincipalFilterToEventFlow x) =
        cauchyPrincipalFilterFromEventFlow (cauchyPrincipalFilterToEventFlow y) :=
    congrArg cauchyPrincipalFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyPrincipalFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyPrincipalFilterTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyPrincipalFilterTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyPrincipalFilterUp, cauchyPrincipalFilterFields x = cauchyPrincipalFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 G1 F1 U1 B1 H1 K1 P1 N1 =>
      cases y with
      | mk A2 G2 F2 U2 B2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance cauchyPrincipalFilterBHistCarrier : BHistCarrier CauchyPrincipalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyPrincipalFilterToEventFlow
  fromEventFlow := cauchyPrincipalFilterFromEventFlow

instance cauchyPrincipalFilterChapterTasteGate : ChapterTasteGate CauchyPrincipalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyPrincipalFilterFromEventFlow (cauchyPrincipalFilterToEventFlow x) = some x
    exact CauchyPrincipalFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyPrincipalFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyPrincipalFilterFieldFaithful : FieldFaithful CauchyPrincipalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyPrincipalFilterFields
  field_faithful := CauchyPrincipalFilterTasteGate_single_carrier_alignment_fields

private def cauchyPrincipalFilterNontrivialDef : Nontrivial CauchyPrincipalFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyPrincipalFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyPrincipalFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance cauchyPrincipalFilterNontrivial : Nontrivial CauchyPrincipalFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyPrincipalFilterNontrivialDef

theorem CauchyPrincipalFilterTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyPrincipalFilterUp) ∧
      Nonempty (FieldFaithful CauchyPrincipalFilterUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyPrincipalFilterUp) ∧
          (∀ h : BHist, cauchyPrincipalFilterDecodeBHist (cauchyPrincipalFilterEncodeBHist h) = h) ∧
            (∀ x : CauchyPrincipalFilterUp,
              cauchyPrincipalFilterFromEventFlow (cauchyPrincipalFilterToEventFlow x) = some x) ∧
              (∀ x y : CauchyPrincipalFilterUp,
                cauchyPrincipalFilterToEventFlow x = cauchyPrincipalFilterToEventFlow y → x = y) ∧
                cauchyPrincipalFilterEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyPrincipalFilterChapterTasteGate⟩,
      ⟨cauchyPrincipalFilterFieldFaithful⟩,
      ⟨cauchyPrincipalFilterNontrivialDef⟩,
      CauchyPrincipalFilterTasteGate_single_carrier_alignment_decode_encode,
      CauchyPrincipalFilterTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyPrincipalFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyPrincipalFilterUp
