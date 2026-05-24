import BEDC.Derived.ComplexUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ComplexUp : Type where
  | mk (real imag carrier classifier ledger nameCert : BHist) : ComplexUp
  deriving DecidableEq

def complexTasteGateTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1]

def complexEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: complexEncodeBHist h
  | BHist.e1 h => BMark.b1 :: complexEncodeBHist h

def complexDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (complexDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (complexDecodeBHist tail)

private theorem ComplexTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, complexDecodeBHist (complexEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def complexFields : ComplexUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ComplexUp.mk real imag carrier classifier ledger nameCert =>
      [real, imag, carrier, classifier, ledger, nameCert]

def complexToEventFlow : ComplexUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ComplexUp.mk real imag carrier classifier ledger nameCert =>
      [complexTasteGateTag, complexEncodeBHist real, complexEncodeBHist imag,
        complexEncodeBHist carrier, complexEncodeBHist classifier, complexEncodeBHist ledger,
        complexEncodeBHist nameCert]

private def complexEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => complexEventAt index rest

def complexFromEventFlow : EventFlow → Option ComplexUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ComplexUp.mk
          (complexDecodeBHist (complexEventAt 1 ef))
          (complexDecodeBHist (complexEventAt 2 ef))
          (complexDecodeBHist (complexEventAt 3 ef))
          (complexDecodeBHist (complexEventAt 4 ef))
          (complexDecodeBHist (complexEventAt 5 ef))
          (complexDecodeBHist (complexEventAt 6 ef)))

private theorem ComplexTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ComplexUp, complexFromEventFlow (complexToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk real imag carrier classifier ledger nameCert =>
      change
        some
          (ComplexUp.mk
            (complexDecodeBHist (complexEncodeBHist real))
            (complexDecodeBHist (complexEncodeBHist imag))
            (complexDecodeBHist (complexEncodeBHist carrier))
            (complexDecodeBHist (complexEncodeBHist classifier))
            (complexDecodeBHist (complexEncodeBHist ledger))
            (complexDecodeBHist (complexEncodeBHist nameCert))) =
          some (ComplexUp.mk real imag carrier classifier ledger nameCert)
      rw [ComplexTasteGate_single_carrier_alignment_decode_encode real,
        ComplexTasteGate_single_carrier_alignment_decode_encode imag,
        ComplexTasteGate_single_carrier_alignment_decode_encode carrier,
        ComplexTasteGate_single_carrier_alignment_decode_encode classifier,
        ComplexTasteGate_single_carrier_alignment_decode_encode ledger,
        ComplexTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem ComplexTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ComplexUp} :
    complexToEventFlow x = complexToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      complexFromEventFlow (complexToEventFlow x) =
        complexFromEventFlow (complexToEventFlow y) :=
    congrArg complexFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ComplexTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ComplexTasteGate_single_carrier_alignment_round_trip y)))

private theorem complexFields_faithful :
    ∀ x y : ComplexUp, complexFields x = complexFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk real₁ imag₁ carrier₁ classifier₁ ledger₁ nameCert₁ =>
      cases y with
      | mk real₂ imag₂ carrier₂ classifier₂ ledger₂ nameCert₂ =>
          cases hfields
          rfl

instance complexBHistCarrier : BHistCarrier ComplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := complexToEventFlow
  fromEventFlow := complexFromEventFlow

instance complexChapterTasteGate : ChapterTasteGate ComplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change complexFromEventFlow (complexToEventFlow x) = some x
    exact ComplexTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ComplexTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance complexFieldFaithful : FieldFaithful ComplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := complexFields
  field_faithful := complexFields_faithful

theorem ComplexTasteGate_single_carrier_alignment :
    (∀ h : BHist, complexDecodeBHist (complexEncodeBHist h) = h) ∧
      (∀ x : ComplexUp, complexFromEventFlow (complexToEventFlow x) = some x) ∧
        (∀ x y : ComplexUp, complexToEventFlow x = complexToEventFlow y → x = y) ∧
          complexEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ComplexTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ComplexTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ComplexTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.ComplexUp
