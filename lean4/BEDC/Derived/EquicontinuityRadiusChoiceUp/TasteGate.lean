import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuityRadiusChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuityRadiusChoiceUp : Type where
  | mk :
      (compactNet finiteFamily equicontinuityRadius rationalFold metricComparison
        uniformModulus realSeal transport replay provenance localCert : BHist) →
      EquicontinuityRadiusChoiceUp
  deriving DecidableEq

def equicontinuityRadiusChoiceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuityRadiusChoiceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuityRadiusChoiceEncodeBHist h

def equicontinuityRadiusChoiceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuityRadiusChoiceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuityRadiusChoiceDecodeBHist tail)

theorem EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      equicontinuityRadiusChoiceDecodeBHist (equicontinuityRadiusChoiceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def equicontinuityRadiusChoiceFields : EquicontinuityRadiusChoiceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuityRadiusChoiceUp.mk compactNet finiteFamily equicontinuityRadius rationalFold
      metricComparison uniformModulus realSeal transport replay provenance localCert =>
      [compactNet, finiteFamily, equicontinuityRadius, rationalFold, metricComparison,
        uniformModulus, realSeal, transport, replay, provenance, localCert]

def equicontinuityRadiusChoiceToEventFlow : EquicontinuityRadiusChoiceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map equicontinuityRadiusChoiceEncodeBHist (equicontinuityRadiusChoiceFields x)

private def EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault index rest

def equicontinuityRadiusChoiceFromEventFlow : EventFlow → Option EquicontinuityRadiusChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (EquicontinuityRadiusChoiceUp.mk
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
        (equicontinuityRadiusChoiceDecodeBHist
          (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_eventAtDefault 10 ef)))

theorem EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EquicontinuityRadiusChoiceUp,
      equicontinuityRadiusChoiceFromEventFlow (equicontinuityRadiusChoiceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactNet finiteFamily equicontinuityRadius rationalFold metricComparison uniformModulus
      realSeal transport replay provenance localCert =>
      change
        some
          (EquicontinuityRadiusChoiceUp.mk
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist compactNet))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist finiteFamily))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist equicontinuityRadius))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist rationalFold))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist metricComparison))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist uniformModulus))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist realSeal))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist transport))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist replay))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist provenance))
            (equicontinuityRadiusChoiceDecodeBHist
              (equicontinuityRadiusChoiceEncodeBHist localCert))) =
          some
            (EquicontinuityRadiusChoiceUp.mk compactNet finiteFamily equicontinuityRadius
              rationalFold metricComparison uniformModulus realSeal transport replay provenance
              localCert)
      rw [EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode compactNet,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode finiteFamily,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode
          equicontinuityRadius,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode rationalFold,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode
          metricComparison,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode uniformModulus,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode realSeal,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode transport,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode replay,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode provenance,
        EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode localCert]

theorem EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EquicontinuityRadiusChoiceUp} :
    equicontinuityRadiusChoiceToEventFlow x = equicontinuityRadiusChoiceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuityRadiusChoiceFromEventFlow (equicontinuityRadiusChoiceToEventFlow x) =
        equicontinuityRadiusChoiceFromEventFlow (equicontinuityRadiusChoiceToEventFlow y) :=
    congrArg equicontinuityRadiusChoiceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_round_trip y)))

private theorem equicontinuityRadiusChoice_field_faithful :
    ∀ x y : EquicontinuityRadiusChoiceUp,
      equicontinuityRadiusChoiceFields x = equicontinuityRadiusChoiceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk compactNet₁ finiteFamily₁ equicontinuityRadius₁ rationalFold₁ metricComparison₁
      uniformModulus₁ realSeal₁ transport₁ replay₁ provenance₁ localCert₁ =>
      cases y with
      | mk compactNet₂ finiteFamily₂ equicontinuityRadius₂ rationalFold₂ metricComparison₂
          uniformModulus₂ realSeal₂ transport₂ replay₂ provenance₂ localCert₂ =>
          cases h
          rfl

instance equicontinuityRadiusChoiceBHistCarrier :
    BHistCarrier EquicontinuityRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuityRadiusChoiceToEventFlow
  fromEventFlow := equicontinuityRadiusChoiceFromEventFlow

instance equicontinuityRadiusChoiceChapterTasteGate :
    ChapterTasteGate EquicontinuityRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      equicontinuityRadiusChoiceFromEventFlow (equicontinuityRadiusChoiceToEventFlow x) =
        some x
    exact EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance equicontinuityRadiusChoiceFieldFaithful :
    FieldFaithful EquicontinuityRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := equicontinuityRadiusChoiceFields
  field_faithful := equicontinuityRadiusChoice_field_faithful

instance equicontinuityRadiusChoiceNontrivial : Nontrivial EquicontinuityRadiusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EquicontinuityRadiusChoiceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EquicontinuityRadiusChoiceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EquicontinuityRadiusChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  equicontinuityRadiusChoiceChapterTasteGate

theorem EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EquicontinuityRadiusChoiceUp) ∧
      Nonempty (FieldFaithful EquicontinuityRadiusChoiceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial EquicontinuityRadiusChoiceUp) ∧
      (∀ h : BHist,
        equicontinuityRadiusChoiceDecodeBHist (equicontinuityRadiusChoiceEncodeBHist h) = h) ∧
      (∀ x : EquicontinuityRadiusChoiceUp,
        equicontinuityRadiusChoiceFromEventFlow (equicontinuityRadiusChoiceToEventFlow x) =
          some x) ∧
      (∀ x y : EquicontinuityRadiusChoiceUp,
        equicontinuityRadiusChoiceToEventFlow x = equicontinuityRadiusChoiceToEventFlow y →
          x = y) ∧
      equicontinuityRadiusChoiceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro equicontinuityRadiusChoiceChapterTasteGate
  · constructor
    · exact Nonempty.intro equicontinuityRadiusChoiceFieldFaithful
    · constructor
      · exact Nonempty.intro equicontinuityRadiusChoiceNontrivial
      · constructor
        · exact EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact
                EquicontinuityRadiusChoiceTasteGate_single_carrier_alignment_toEventFlow_injective
                  heq
            · rfl

end BEDC.Derived.EquicontinuityRadiusChoiceUp
