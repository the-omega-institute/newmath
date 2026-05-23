import BEDC.Derived.CauchyRealApartnessUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealApartnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyRealApartnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealApartnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealApartnessEncodeBHist h

def cauchyRealApartnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealApartnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealApartnessDecodeBHist tail)

private theorem CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyRealApartnessFields : CauchyRealApartnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealApartnessUp.mk E0 E1 R0 R1 W0 W1 D T H C P N =>
      [E0, E1, R0, R1, W0, W1, D, T, H, C, P, N]

def cauchyRealApartnessToEventFlow : CauchyRealApartnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealApartnessFields x).map cauchyRealApartnessEncodeBHist

private def CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt index rest

def cauchyRealApartnessFromEventFlow (ef : EventFlow) :
    Option CauchyRealApartnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRealApartnessUp.mk
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 0 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 1 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 2 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 3 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 4 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 5 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 6 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 7 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 8 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 9 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 10 ef))
      (cauchyRealApartnessDecodeBHist
        (CauchyRealApartnessTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem CauchyRealApartnessTasteGate_single_carrier_alignment_round_trip
    (x : CauchyRealApartnessUp) :
    cauchyRealApartnessFromEventFlow (cauchyRealApartnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E0 E1 R0 R1 W0 W1 D T H C P N =>
      change
        some
          (CauchyRealApartnessUp.mk
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist E0))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist E1))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist R0))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist R1))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist W0))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist W1))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist D))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist T))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist H))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist C))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist P))
            (cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist N))) =
          some (CauchyRealApartnessUp.mk E0 E1 R0 R1 W0 W1 D T H C P N)
      rw [CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode E0,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode E1,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode R0,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode R1,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode W0,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode W1,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode T,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRealApartnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealApartnessUp} :
    cauchyRealApartnessToEventFlow x = cauchyRealApartnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealApartnessFromEventFlow (cauchyRealApartnessToEventFlow x) =
        cauchyRealApartnessFromEventFlow (cauchyRealApartnessToEventFlow y) :=
    congrArg cauchyRealApartnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRealApartnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRealApartnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyRealApartnessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyRealApartnessUp,
      cauchyRealApartnessFields x = cauchyRealApartnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E0₁ E1₁ R0₁ R1₁ W0₁ W1₁ D₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E0₂ E1₂ R0₂ R1₂ W0₂ W1₂ D₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyRealApartnessBHistCarrier : BHistCarrier CauchyRealApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealApartnessToEventFlow
  fromEventFlow := cauchyRealApartnessFromEventFlow

instance cauchyRealApartnessChapterTasteGate :
    ChapterTasteGate CauchyRealApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRealApartnessFromEventFlow (cauchyRealApartnessToEventFlow x) = some x
    exact CauchyRealApartnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRealApartnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRealApartnessFieldFaithful : FieldFaithful CauchyRealApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRealApartnessFields
  field_faithful := CauchyRealApartnessTasteGate_single_carrier_alignment_fields_faithful

instance cauchyRealApartnessNontrivial : Nontrivial CauchyRealApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRealApartnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      CauchyRealApartnessUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyRealApartnessTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyRealApartnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRealApartnessChapterTasteGate

theorem CauchyRealApartnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRealApartnessDecodeBHist (cauchyRealApartnessEncodeBHist h) = h) ∧
      (∀ x : CauchyRealApartnessUp,
        cauchyRealApartnessFromEventFlow (cauchyRealApartnessToEventFlow x) = some x) ∧
        (∀ x y : CauchyRealApartnessUp,
          cauchyRealApartnessToEventFlow x = cauchyRealApartnessToEventFlow y → x = y) ∧
          cauchyRealApartnessEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : CauchyRealApartnessUp,
              cauchyRealApartnessFields x = cauchyRealApartnessFields y → x = y) ∧
              (∃ x y : CauchyRealApartnessUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨CauchyRealApartnessTasteGate_single_carrier_alignment_decode_encode,
      CauchyRealApartnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyRealApartnessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      CauchyRealApartnessTasteGate_single_carrier_alignment_fields_faithful,
      ⟨CauchyRealApartnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        CauchyRealApartnessUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.CauchyRealApartnessUp
