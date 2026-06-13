import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyWindowComparisonPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyWindowComparisonPrincipleUp : Type where
  | mk (S0 S1 D R0 R1 E H C P N : BHist) :
      CauchyWindowComparisonPrincipleUp
  deriving DecidableEq

def cauchyWindowComparisonPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyWindowComparisonPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyWindowComparisonPrincipleEncodeBHist h

def cauchyWindowComparisonPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyWindowComparisonPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyWindowComparisonPrincipleDecodeBHist tail)

private theorem CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyWindowComparisonPrincipleDecodeBHist
          (cauchyWindowComparisonPrincipleEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyWindowComparisonPrincipleFields :
    CauchyWindowComparisonPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyWindowComparisonPrincipleUp.mk S0 S1 D R0 R1 E H C P N =>
      [S0, S1, D, R0, R1, E, H, C, P, N]

def cauchyWindowComparisonPrincipleToEventFlow :
    CauchyWindowComparisonPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map cauchyWindowComparisonPrincipleEncodeBHist
        (cauchyWindowComparisonPrincipleFields x)

private def cauchyWindowComparisonPrincipleRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyWindowComparisonPrincipleRawAt index rest

def cauchyWindowComparisonPrincipleFromEventFlow
    (flow : EventFlow) : Option CauchyWindowComparisonPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyWindowComparisonPrincipleUp.mk
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 0 flow))
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 1 flow))
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 2 flow))
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 3 flow))
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 4 flow))
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 5 flow))
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 6 flow))
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 7 flow))
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 8 flow))
      (cauchyWindowComparisonPrincipleDecodeBHist
        (cauchyWindowComparisonPrincipleRawAt 9 flow)))

private theorem CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_round_trip
    (x : CauchyWindowComparisonPrincipleUp) :
    cauchyWindowComparisonPrincipleFromEventFlow
        (cauchyWindowComparisonPrincipleToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S0 S1 D R0 R1 E H C P N =>
      change
        some
          (CauchyWindowComparisonPrincipleUp.mk
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist S0))
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist S1))
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist D))
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist R0))
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist R1))
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist E))
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist H))
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist C))
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist P))
            (cauchyWindowComparisonPrincipleDecodeBHist
              (cauchyWindowComparisonPrincipleEncodeBHist N))) =
          some (CauchyWindowComparisonPrincipleUp.mk S0 S1 D R0 R1 E H C P N)
      rw [CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode S0,
        CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode S1,
        CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode D,
        CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode R0,
        CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode R1,
        CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode E,
        CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode H,
        CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode C,
        CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode P,
        CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_ToEventFlow_injective
    {x y : CauchyWindowComparisonPrincipleUp} :
    cauchyWindowComparisonPrincipleToEventFlow x =
        cauchyWindowComparisonPrincipleToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyWindowComparisonPrincipleFromEventFlow
          (cauchyWindowComparisonPrincipleToEventFlow x) =
        cauchyWindowComparisonPrincipleFromEventFlow
          (cauchyWindowComparisonPrincipleToEventFlow y) :=
    congrArg cauchyWindowComparisonPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyWindowComparisonPrincipleUp,
      cauchyWindowComparisonPrincipleFields x =
        cauchyWindowComparisonPrincipleFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S0₁ S1₁ D₁ R0₁ R1₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S0₂ S1₂ D₂ R0₂ R1₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyWindowComparisonPrincipleBHistCarrier :
    BHistCarrier CauchyWindowComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyWindowComparisonPrincipleToEventFlow
  fromEventFlow := cauchyWindowComparisonPrincipleFromEventFlow

instance cauchyWindowComparisonPrincipleChapterTasteGate :
    ChapterTasteGate CauchyWindowComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyWindowComparisonPrincipleFromEventFlow
          (cauchyWindowComparisonPrincipleToEventFlow x) =
        some x
    exact CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_ToEventFlow_injective
        heq)

instance cauchyWindowComparisonPrincipleFieldFaithful :
    FieldFaithful CauchyWindowComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyWindowComparisonPrincipleFields
  field_faithful :=
    CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_fields_faithful

instance cauchyWindowComparisonPrincipleNontrivial :
    Nontrivial CauchyWindowComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyWindowComparisonPrincipleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyWindowComparisonPrincipleUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyWindowComparisonPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyWindowComparisonPrincipleChapterTasteGate

theorem CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyWindowComparisonPrincipleDecodeBHist
          (cauchyWindowComparisonPrincipleEncodeBHist h) =
        h) ∧
      (∀ x : CauchyWindowComparisonPrincipleUp,
        cauchyWindowComparisonPrincipleFromEventFlow
            (cauchyWindowComparisonPrincipleToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyWindowComparisonPrincipleUp,
          cauchyWindowComparisonPrincipleToEventFlow x =
              cauchyWindowComparisonPrincipleToEventFlow y →
            x = y) ∧
          cauchyWindowComparisonPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_decode_encode,
      CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact
          CauchyWindowComparisonPrincipleTasteGate_single_carrier_alignment_ToEventFlow_injective
            heq,
      rfl⟩

end BEDC.Derived.CauchyWindowComparisonPrincipleUp
