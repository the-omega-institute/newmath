import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AnalogyCertificateGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AnalogyCertificateGateUp : Type where
  | mk :
      (source kernel gate relation vertex universeRow ledger evidence fiber hom carrier
        provenance nameCert : BHist) →
      AnalogyCertificateGateUp
  deriving DecidableEq

def analogyCertificateGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: analogyCertificateGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: analogyCertificateGateEncodeBHist h

def analogyCertificateGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (analogyCertificateGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (analogyCertificateGateDecodeBHist tail)

private theorem AnalogyCertificateGateUp_single_carrier_alignment_decode :
    ∀ h : BHist, analogyCertificateGateDecodeBHist
      (analogyCertificateGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def analogyCertificateGateFields : AnalogyCertificateGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AnalogyCertificateGateUp.mk source kernel gate relation vertex universeRow ledger evidence
      fiber hom carrier provenance nameCert =>
      [source, kernel, gate, relation, vertex, universeRow, ledger, evidence, fiber, hom,
        carrier, provenance, nameCert]

def analogyCertificateGateToEventFlow : AnalogyCertificateGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AnalogyCertificateGateUp.mk source kernel gate relation vertex universeRow ledger evidence
      fiber hom carrier provenance nameCert =>
      [[BMark.b0],
        analogyCertificateGateEncodeBHist source,
        [BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist kernel,
        [BMark.b1, BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist gate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist relation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist vertex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist universeRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        analogyCertificateGateEncodeBHist evidence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist fiber,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist hom,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist carrier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        analogyCertificateGateEncodeBHist nameCert]

private def AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault index rest

def analogyCertificateGateFromEventFlow
    (ef : EventFlow) : Option AnalogyCertificateGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AnalogyCertificateGateUp.mk
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 1 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 3 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 5 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 7 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 9 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 11 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 13 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 15 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 17 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 19 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 21 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 23 ef))
      (analogyCertificateGateDecodeBHist
        (AnalogyCertificateGateUp_single_carrier_alignment_eventAtDefault 25 ef)))

private theorem AnalogyCertificateGateUp_single_carrier_alignment_round_trip :
    ∀ x : AnalogyCertificateGateUp,
      analogyCertificateGateFromEventFlow (analogyCertificateGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source kernel gate relation vertex universeRow ledger evidence fiber hom carrier
      provenance nameCert =>
      change
        some
          (AnalogyCertificateGateUp.mk
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist source))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist kernel))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist gate))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist relation))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist vertex))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist universeRow))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist ledger))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist evidence))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist fiber))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist hom))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist carrier))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist provenance))
            (analogyCertificateGateDecodeBHist (analogyCertificateGateEncodeBHist nameCert))) =
          some
            (AnalogyCertificateGateUp.mk source kernel gate relation vertex universeRow ledger
              evidence fiber hom carrier provenance nameCert)
      rw [AnalogyCertificateGateUp_single_carrier_alignment_decode source,
        AnalogyCertificateGateUp_single_carrier_alignment_decode kernel,
        AnalogyCertificateGateUp_single_carrier_alignment_decode gate,
        AnalogyCertificateGateUp_single_carrier_alignment_decode relation,
        AnalogyCertificateGateUp_single_carrier_alignment_decode vertex,
        AnalogyCertificateGateUp_single_carrier_alignment_decode universeRow,
        AnalogyCertificateGateUp_single_carrier_alignment_decode ledger,
        AnalogyCertificateGateUp_single_carrier_alignment_decode evidence,
        AnalogyCertificateGateUp_single_carrier_alignment_decode fiber,
        AnalogyCertificateGateUp_single_carrier_alignment_decode hom,
        AnalogyCertificateGateUp_single_carrier_alignment_decode carrier,
        AnalogyCertificateGateUp_single_carrier_alignment_decode provenance,
        AnalogyCertificateGateUp_single_carrier_alignment_decode nameCert]

private theorem AnalogyCertificateGateUp_single_carrier_alignment_injective
    {x y : AnalogyCertificateGateUp} :
    analogyCertificateGateToEventFlow x = analogyCertificateGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      analogyCertificateGateFromEventFlow (analogyCertificateGateToEventFlow x) =
        analogyCertificateGateFromEventFlow (analogyCertificateGateToEventFlow y) :=
    congrArg analogyCertificateGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AnalogyCertificateGateUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AnalogyCertificateGateUp_single_carrier_alignment_round_trip y)))

private theorem AnalogyCertificateGateUp_single_carrier_alignment_fields :
    ∀ x y : AnalogyCertificateGateUp,
      analogyCertificateGateFields x = analogyCertificateGateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ kernel₁ gate₁ relation₁ vertex₁ universeRow₁ ledger₁ evidence₁ fiber₁ hom₁
      carrier₁ provenance₁ nameCert₁ =>
      cases y with
      | mk source₂ kernel₂ gate₂ relation₂ vertex₂ universeRow₂ ledger₂ evidence₂ fiber₂ hom₂
          carrier₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance analogyCertificateGateBHistCarrier : BHistCarrier AnalogyCertificateGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := analogyCertificateGateToEventFlow
  fromEventFlow := analogyCertificateGateFromEventFlow

instance analogyCertificateGateChapterTasteGate :
    ChapterTasteGate AnalogyCertificateGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change analogyCertificateGateFromEventFlow (analogyCertificateGateToEventFlow x) = some x
    exact AnalogyCertificateGateUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AnalogyCertificateGateUp_single_carrier_alignment_injective heq)

instance analogyCertificateGateFieldFaithful : FieldFaithful AnalogyCertificateGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := analogyCertificateGateFields
  field_faithful := AnalogyCertificateGateUp_single_carrier_alignment_fields

instance analogyCertificateGateNontrivial : Nontrivial AnalogyCertificateGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AnalogyCertificateGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AnalogyCertificateGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AnalogyCertificateGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  analogyCertificateGateChapterTasteGate

theorem AnalogyCertificateGateUp_single_carrier_alignment :
    (∀ h : BHist, analogyCertificateGateDecodeBHist
      (analogyCertificateGateEncodeBHist h) = h) ∧
      (∀ x : AnalogyCertificateGateUp,
        analogyCertificateGateFromEventFlow (analogyCertificateGateToEventFlow x) = some x) ∧
        (∀ x y : AnalogyCertificateGateUp,
          analogyCertificateGateToEventFlow x = analogyCertificateGateToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate AnalogyCertificateGateUp) ∧
            (∀ x y : AnalogyCertificateGateUp,
              analogyCertificateGateFields x = analogyCertificateGateFields y → x = y) ∧
              (∀ x : AnalogyCertificateGateUp,
                ∃ h : BHist, List.Mem h (analogyCertificateGateFields x)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact AnalogyCertificateGateUp_single_carrier_alignment_decode
  · constructor
    · exact AnalogyCertificateGateUp_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact AnalogyCertificateGateUp_single_carrier_alignment_injective heq
      · constructor
        · exact ⟨analogyCertificateGateChapterTasteGate⟩
        · constructor
          · exact AnalogyCertificateGateUp_single_carrier_alignment_fields
          · intro x
            cases x with
            | mk source kernel gate relation vertex universeRow ledger evidence fiber hom carrier
                provenance nameCert =>
                exact ⟨source, List.Mem.head _⟩

end BEDC.Derived.AnalogyCertificateGateUp
