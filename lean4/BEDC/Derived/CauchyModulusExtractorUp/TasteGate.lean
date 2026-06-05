import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusExtractorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusExtractorUp : Type where
  | mk (E F M S D Q R H C P N : BHist) : CauchyModulusExtractorUp
  deriving DecidableEq

def cauchyModulusExtractorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusExtractorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusExtractorEncodeBHist h

def cauchyModulusExtractorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusExtractorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusExtractorDecodeBHist tail)

private theorem CauchyModulusExtractorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusExtractorFields : CauchyModulusExtractorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusExtractorUp.mk E F M S D Q R H C P N =>
      [E, F, M, S, D, Q, R, H, C, P, N]

def cauchyModulusExtractorToEventFlow : CauchyModulusExtractorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyModulusExtractorFields x).map cauchyModulusExtractorEncodeBHist

private def cauchyModulusExtractorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusExtractorEventAtDefault index rest

def cauchyModulusExtractorFromEventFlow
    (ef : EventFlow) : Option CauchyModulusExtractorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusExtractorUp.mk
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 0 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 1 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 2 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 3 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 4 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 5 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 6 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 7 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 8 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 9 ef))
      (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEventAtDefault 10 ef)))

private theorem CauchyModulusExtractorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyModulusExtractorUp,
      cauchyModulusExtractorFromEventFlow (cauchyModulusExtractorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E F M S D Q R H C P N =>
      change
        some
          (CauchyModulusExtractorUp.mk
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist E))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist F))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist M))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist S))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist D))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist Q))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist R))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist H))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist C))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist P))
            (cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist N))) =
          some (CauchyModulusExtractorUp.mk E F M S D Q R H C P N)
      rw [CauchyModulusExtractorTasteGate_single_carrier_alignment_decode E,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode F,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode M,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode S,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode D,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode Q,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode R,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode H,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode C,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode P,
        CauchyModulusExtractorTasteGate_single_carrier_alignment_decode N]

private theorem CauchyModulusExtractorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyModulusExtractorUp} :
    cauchyModulusExtractorToEventFlow x = cauchyModulusExtractorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusExtractorFromEventFlow (cauchyModulusExtractorToEventFlow x) =
        cauchyModulusExtractorFromEventFlow (cauchyModulusExtractorToEventFlow y) :=
    congrArg cauchyModulusExtractorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyModulusExtractorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyModulusExtractorTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyModulusExtractorTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyModulusExtractorUp,
      cauchyModulusExtractorFields x = cauchyModulusExtractorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ F₁ M₁ S₁ D₁ Q₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ F₂ M₂ S₂ D₂ Q₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyModulusExtractorBHistCarrier :
    BHistCarrier CauchyModulusExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusExtractorToEventFlow
  fromEventFlow := cauchyModulusExtractorFromEventFlow

instance cauchyModulusExtractorChapterTasteGate :
    ChapterTasteGate CauchyModulusExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusExtractorFromEventFlow (cauchyModulusExtractorToEventFlow x) =
        some x
    exact CauchyModulusExtractorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyModulusExtractorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyModulusExtractorFieldFaithful :
    FieldFaithful CauchyModulusExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyModulusExtractorFields
  field_faithful := CauchyModulusExtractorTasteGate_single_carrier_alignment_fields

instance cauchyModulusExtractorNontrivial :
    Nontrivial CauchyModulusExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyModulusExtractorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyModulusExtractorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyModulusExtractorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusExtractorChapterTasteGate

theorem CauchyModulusExtractorTasteGate_single_carrier_alignment :
    cauchyModulusExtractorEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      (∀ h : BHist,
        cauchyModulusExtractorDecodeBHist (cauchyModulusExtractorEncodeBHist h) = h) ∧
        Nonempty (BHistCarrier CauchyModulusExtractorUp) ∧
          Nonempty (ChapterTasteGate CauchyModulusExtractorUp) ∧
            ∀ x : CauchyModulusExtractorUp,
              cauchyModulusExtractorFromEventFlow (cauchyModulusExtractorToEventFlow x) =
                some x := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨rfl,
      CauchyModulusExtractorTasteGate_single_carrier_alignment_decode,
      ⟨cauchyModulusExtractorBHistCarrier⟩,
      ⟨cauchyModulusExtractorChapterTasteGate⟩,
      CauchyModulusExtractorTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.CauchyModulusExtractorUp
