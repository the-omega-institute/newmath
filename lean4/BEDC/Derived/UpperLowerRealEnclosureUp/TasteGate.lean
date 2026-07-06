import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpperLowerRealEnclosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpperLowerRealEnclosureUp : Type where
  | mk
      (lower upper width schedule readback realSeal transport replay provenance localCert :
        BHist) :
      UpperLowerRealEnclosureUp

def upperLowerRealEnclosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: upperLowerRealEnclosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: upperLowerRealEnclosureEncodeBHist h

def upperLowerRealEnclosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (upperLowerRealEnclosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (upperLowerRealEnclosureDecodeBHist tail)

private theorem upperLowerRealEnclosure_decode_encode_bhist :
    ∀ h : BHist,
      upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def upperLowerRealEnclosureFields : UpperLowerRealEnclosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UpperLowerRealEnclosureUp.mk lower upper width schedule readback realSeal transport replay
      provenance localCert =>
      [lower, upper, width, schedule, readback, realSeal, transport, replay, provenance,
        localCert]

def upperLowerRealEnclosureToEventFlow : UpperLowerRealEnclosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (upperLowerRealEnclosureFields x).map upperLowerRealEnclosureEncodeBHist

private def upperLowerRealEnclosureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => upperLowerRealEnclosureEventAtDefault index rest

def upperLowerRealEnclosureFromEventFlow (ef : EventFlow) :
    Option UpperLowerRealEnclosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UpperLowerRealEnclosureUp.mk
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 0 ef))
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 1 ef))
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 2 ef))
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 3 ef))
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 4 ef))
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 5 ef))
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 6 ef))
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 7 ef))
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 8 ef))
      (upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEventAtDefault 9 ef)))

private theorem upperLowerRealEnclosure_round_trip :
    ∀ x : UpperLowerRealEnclosureUp,
      upperLowerRealEnclosureFromEventFlow
        (upperLowerRealEnclosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lower upper width schedule readback realSeal transport replay provenance localCert =>
      change
        some
          (UpperLowerRealEnclosureUp.mk
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist lower))
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist upper))
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist width))
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist schedule))
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist readback))
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist realSeal))
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist transport))
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist replay))
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist provenance))
            (upperLowerRealEnclosureDecodeBHist
              (upperLowerRealEnclosureEncodeBHist localCert))) =
          some
            (UpperLowerRealEnclosureUp.mk lower upper width schedule readback realSeal
              transport replay provenance localCert)
      rw [upperLowerRealEnclosure_decode_encode_bhist lower,
        upperLowerRealEnclosure_decode_encode_bhist upper,
        upperLowerRealEnclosure_decode_encode_bhist width,
        upperLowerRealEnclosure_decode_encode_bhist schedule,
        upperLowerRealEnclosure_decode_encode_bhist readback,
        upperLowerRealEnclosure_decode_encode_bhist realSeal,
        upperLowerRealEnclosure_decode_encode_bhist transport,
        upperLowerRealEnclosure_decode_encode_bhist replay,
        upperLowerRealEnclosure_decode_encode_bhist provenance,
        upperLowerRealEnclosure_decode_encode_bhist localCert]

private theorem upperLowerRealEnclosureToEventFlow_injective
    {x y : UpperLowerRealEnclosureUp} :
    upperLowerRealEnclosureToEventFlow x = upperLowerRealEnclosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      upperLowerRealEnclosureFromEventFlow (upperLowerRealEnclosureToEventFlow x) =
        upperLowerRealEnclosureFromEventFlow (upperLowerRealEnclosureToEventFlow y) :=
    congrArg upperLowerRealEnclosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (upperLowerRealEnclosure_round_trip x).symm
      (Eq.trans hread (upperLowerRealEnclosure_round_trip y)))

private theorem upperLowerRealEnclosure_fields_faithful :
    ∀ x y : UpperLowerRealEnclosureUp,
      upperLowerRealEnclosureFields x = upperLowerRealEnclosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk lower₁ upper₁ width₁ schedule₁ readback₁ realSeal₁ transport₁ replay₁
      provenance₁ localCert₁ =>
      cases y with
      | mk lower₂ upper₂ width₂ schedule₂ readback₂ realSeal₂ transport₂ replay₂
          provenance₂ localCert₂ =>
          cases hfields
          rfl

instance upperLowerRealEnclosureBHistCarrier :
    BHistCarrier UpperLowerRealEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := upperLowerRealEnclosureToEventFlow
  fromEventFlow := upperLowerRealEnclosureFromEventFlow

instance upperLowerRealEnclosureChapterTasteGate :
    ChapterTasteGate UpperLowerRealEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      upperLowerRealEnclosureFromEventFlow
        (upperLowerRealEnclosureToEventFlow x) = some x
    exact upperLowerRealEnclosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (upperLowerRealEnclosureToEventFlow_injective heq)

instance upperLowerRealEnclosureFieldFaithful :
    FieldFaithful UpperLowerRealEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := upperLowerRealEnclosureFields
  field_faithful := upperLowerRealEnclosure_fields_faithful

instance upperLowerRealEnclosureNontrivial :
    Nontrivial UpperLowerRealEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UpperLowerRealEnclosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UpperLowerRealEnclosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UpperLowerRealEnclosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  upperLowerRealEnclosureChapterTasteGate

def taste_gate_witness : FieldFaithful UpperLowerRealEnclosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  upperLowerRealEnclosureFieldFaithful

theorem UpperLowerRealEnclosureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UpperLowerRealEnclosureUp) ∧
      Nonempty (FieldFaithful UpperLowerRealEnclosureUp) ∧
        Nonempty (Nontrivial UpperLowerRealEnclosureUp) ∧
          (∀ h : BHist,
            upperLowerRealEnclosureDecodeBHist (upperLowerRealEnclosureEncodeBHist h) = h) ∧
            (∀ x : UpperLowerRealEnclosureUp,
              upperLowerRealEnclosureFromEventFlow
                (upperLowerRealEnclosureToEventFlow x) = some x) ∧
              upperLowerRealEnclosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro upperLowerRealEnclosureChapterTasteGate,
      Nonempty.intro upperLowerRealEnclosureFieldFaithful,
      Nonempty.intro upperLowerRealEnclosureNontrivial,
      upperLowerRealEnclosure_decode_encode_bhist,
      upperLowerRealEnclosure_round_trip,
      rfl⟩

end BEDC.Derived.UpperLowerRealEnclosureUp
