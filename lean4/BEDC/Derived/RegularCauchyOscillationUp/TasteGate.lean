import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyOscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyOscillationUp : Type where
  | mk (schedule window readback tolerance ledger realSeal transport replay provenance localName :
      BHist) : RegularCauchyOscillationUp
  deriving DecidableEq

def regularCauchyOscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyOscillationEncodeBHist h

def regularCauchyOscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyOscillationDecodeBHist tail)

private theorem RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyOscillationDecodeBHist (regularCauchyOscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyOscillationFields : RegularCauchyOscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyOscillationUp.mk schedule window readback tolerance ledger realSeal transport replay
      provenance localName =>
      [schedule, window, readback, tolerance, ledger, realSeal, transport, replay, provenance,
        localName]

def regularCauchyOscillationToEventFlow : RegularCauchyOscillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyOscillationFields x).map regularCauchyOscillationEncodeBHist

private def regularCauchyOscillationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyOscillationEventAt index rest

def regularCauchyOscillationFromEventFlow (ef : EventFlow) :
    Option RegularCauchyOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyOscillationUp.mk
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 0 ef))
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 1 ef))
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 2 ef))
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 3 ef))
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 4 ef))
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 5 ef))
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 6 ef))
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 7 ef))
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 8 ef))
      (regularCauchyOscillationDecodeBHist (regularCauchyOscillationEventAt 9 ef)))

private theorem RegularCauchyOscillationTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyOscillationUp) :
    regularCauchyOscillationFromEventFlow (regularCauchyOscillationToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk schedule window readback tolerance ledger realSeal transport replay provenance localName =>
      change
        some
          (RegularCauchyOscillationUp.mk
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist schedule))
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist window))
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist readback))
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist tolerance))
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist ledger))
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist realSeal))
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist transport))
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist replay))
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist provenance))
            (regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist localName))) =
          some
            (RegularCauchyOscillationUp.mk schedule window readback tolerance ledger realSeal
              transport replay provenance localName)
      rw [RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode schedule,
        RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode window,
        RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode readback,
        RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode tolerance,
        RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode ledger,
        RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode realSeal,
        RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode transport,
        RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode replay,
        RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode provenance,
        RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode localName]

private theorem RegularCauchyOscillationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyOscillationUp} :
    regularCauchyOscillationToEventFlow x = regularCauchyOscillationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyOscillationFromEventFlow (regularCauchyOscillationToEventFlow x) =
        regularCauchyOscillationFromEventFlow (regularCauchyOscillationToEventFlow y) :=
    congrArg regularCauchyOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyOscillationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyOscillationTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyOscillationTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyOscillationUp,
      regularCauchyOscillationFields x = regularCauchyOscillationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk schedule₁ window₁ readback₁ tolerance₁ ledger₁ realSeal₁ transport₁ replay₁ provenance₁
      localName₁ =>
      cases y with
      | mk schedule₂ window₂ readback₂ tolerance₂ ledger₂ realSeal₂ transport₂ replay₂ provenance₂
          localName₂ =>
          cases hfields
          rfl

instance regularCauchyOscillationBHistCarrier :
    BHistCarrier RegularCauchyOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyOscillationToEventFlow
  fromEventFlow := regularCauchyOscillationFromEventFlow

instance regularCauchyOscillationChapterTasteGate :
    ChapterTasteGate RegularCauchyOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyOscillationFromEventFlow
      (regularCauchyOscillationToEventFlow x) = some x
    exact RegularCauchyOscillationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyOscillationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyOscillationFieldFaithful :
    FieldFaithful RegularCauchyOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyOscillationFields
  field_faithful :=
    RegularCauchyOscillationTasteGate_single_carrier_alignment_field_faithful

instance regularCauchyOscillationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyOscillationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyOscillationUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyOscillationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyOscillationUp) ∧
      Nonempty (FieldFaithful RegularCauchyOscillationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyOscillationUp) ∧
          (∀ h : BHist,
            regularCauchyOscillationDecodeBHist
              (regularCauchyOscillationEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyOscillationUp,
              regularCauchyOscillationFromEventFlow
                (regularCauchyOscillationToEventFlow x) = some x) ∧
              regularCauchyOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨regularCauchyOscillationChapterTasteGate⟩,
      ⟨regularCauchyOscillationFieldFaithful⟩, ⟨regularCauchyOscillationNontrivial⟩,
      RegularCauchyOscillationTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyOscillationTasteGate_single_carrier_alignment_round_trip, rfl⟩

end BEDC.Derived.RegularCauchyOscillationUp
