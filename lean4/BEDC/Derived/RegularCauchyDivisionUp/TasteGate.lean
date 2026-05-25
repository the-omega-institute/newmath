import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDivisionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDivisionUp : Type where
  | mk
      (numerator denominator apartness reciprocal product windows readback realSeal transport
        continuation provenance localName : BHist) :
      RegularCauchyDivisionUp
  deriving DecidableEq

def regularCauchyDivisionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDivisionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDivisionEncodeBHist h

def regularCauchyDivisionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDivisionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDivisionDecodeBHist tail)

private theorem RegularCauchyDivisionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDivisionFields : RegularCauchyDivisionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDivisionUp.mk numerator denominator apartness reciprocal product windows
      readback realSeal transport continuation provenance localName =>
      [numerator, denominator, apartness, reciprocal, product, windows, readback, realSeal,
        transport, continuation, provenance, localName]

def regularCauchyDivisionToEventFlow : RegularCauchyDivisionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDivisionUp.mk numerator denominator apartness reciprocal product windows
      readback realSeal transport continuation provenance localName =>
      [regularCauchyDivisionEncodeBHist numerator,
        regularCauchyDivisionEncodeBHist denominator,
        regularCauchyDivisionEncodeBHist apartness,
        regularCauchyDivisionEncodeBHist reciprocal,
        regularCauchyDivisionEncodeBHist product,
        regularCauchyDivisionEncodeBHist windows,
        regularCauchyDivisionEncodeBHist readback,
        regularCauchyDivisionEncodeBHist realSeal,
        regularCauchyDivisionEncodeBHist transport,
        regularCauchyDivisionEncodeBHist continuation,
        regularCauchyDivisionEncodeBHist provenance,
        regularCauchyDivisionEncodeBHist localName]

private def RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault index rest

def regularCauchyDivisionFromEventFlow
    (ef : EventFlow) : Option RegularCauchyDivisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyDivisionUp.mk
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (regularCauchyDivisionDecodeBHist
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

private theorem RegularCauchyDivisionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyDivisionUp,
      regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk numerator denominator apartness reciprocal product windows readback realSeal transport
      continuation provenance localName =>
      change
        some
          (RegularCauchyDivisionUp.mk
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist numerator))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist denominator))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist apartness))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist reciprocal))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist product))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist windows))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist readback))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist realSeal))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist transport))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist continuation))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist provenance))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist localName))) =
          some
            (RegularCauchyDivisionUp.mk numerator denominator apartness reciprocal product
              windows readback realSeal transport continuation provenance localName)
      rw [RegularCauchyDivisionTasteGate_single_carrier_alignment_decode numerator,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode denominator,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode apartness,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode reciprocal,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode product,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode windows,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode readback,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode realSeal,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode transport,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode continuation,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode provenance,
        RegularCauchyDivisionTasteGate_single_carrier_alignment_decode localName]

private theorem RegularCauchyDivisionTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyDivisionUp} :
    regularCauchyDivisionToEventFlow x = regularCauchyDivisionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x = regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow x) :=
        (RegularCauchyDivisionTasteGate_single_carrier_alignment_round_trip x).symm
      _ = regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow y) :=
        congrArg regularCauchyDivisionFromEventFlow heq
      _ = some y := RegularCauchyDivisionTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem RegularCauchyDivisionTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyDivisionUp, regularCauchyDivisionFields x =
      regularCauchyDivisionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk numerator₁ denominator₁ apartness₁ reciprocal₁ product₁ windows₁ readback₁
      realSeal₁ transport₁ continuation₁ provenance₁ localName₁ =>
      cases y with
      | mk numerator₂ denominator₂ apartness₂ reciprocal₂ product₂ windows₂ readback₂
          realSeal₂ transport₂ continuation₂ provenance₂ localName₂ =>
          cases h
          rfl

instance regularCauchyDivisionBHistCarrier : BHistCarrier RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDivisionToEventFlow
  fromEventFlow := regularCauchyDivisionFromEventFlow

instance regularCauchyDivisionChapterTasteGate :
    ChapterTasteGate RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow x) = some x
    exact RegularCauchyDivisionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyDivisionTasteGate_single_carrier_alignment_injective heq)

instance regularCauchyDivisionFieldFaithful : FieldFaithful RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyDivisionFields
  field_faithful := RegularCauchyDivisionTasteGate_single_carrier_alignment_field_faithful

instance regularCauchyDivisionNontrivial : Nontrivial RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyDivisionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyDivisionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def regularCauchyDivisionTasteGate : ChapterTasteGate RegularCauchyDivisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDivisionChapterTasteGate

theorem RegularCauchyDivisionTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyDivisionDecodeBHist
      (regularCauchyDivisionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyDivisionUp, regularCauchyDivisionFromEventFlow
        (regularCauchyDivisionToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyDivisionUp,
          regularCauchyDivisionToEventFlow x =
            regularCauchyDivisionToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate RegularCauchyDivisionUp) ∧
            Nonempty (FieldFaithful RegularCauchyDivisionUp) ∧
              Nonempty (Nontrivial RegularCauchyDivisionUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact RegularCauchyDivisionTasteGate_single_carrier_alignment_decode
  · constructor
    · exact RegularCauchyDivisionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact RegularCauchyDivisionTasteGate_single_carrier_alignment_injective heq
      · exact
          ⟨⟨regularCauchyDivisionChapterTasteGate⟩,
            ⟨regularCauchyDivisionFieldFaithful⟩,
            ⟨regularCauchyDivisionNontrivial⟩⟩

end BEDC.Derived.RegularCauchyDivisionUp.TasteGate
