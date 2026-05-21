import BEDC.Derived.BitVectorUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BitVectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BitVectorUp : Type where
  | mk (width spine ledger provenance : BHist) : BitVectorUp
  deriving DecidableEq

def bitVectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bitVectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bitVectorEncodeBHist h

def bitVectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bitVectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bitVectorDecodeBHist tail)

private theorem BitVectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bitVectorDecodeBHist (bitVectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bitVectorFields : BitVectorUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BitVectorUp.mk width spine ledger provenance =>
      [width, spine, ledger, provenance]

def bitVectorToEventFlow : BitVectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bitVectorFields x).map bitVectorEncodeBHist

def bitVectorFromEventFlow : EventFlow → Option BitVectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | width :: rest0 =>
      match rest0 with
      | [] => none
      | spine :: rest1 =>
          match rest1 with
          | [] => none
          | ledger :: rest2 =>
              match rest2 with
              | [] => none
              | provenance :: rest3 =>
                  match rest3 with
                  | [] =>
                      some
                        (BitVectorUp.mk
                          (bitVectorDecodeBHist width)
                          (bitVectorDecodeBHist spine)
                          (bitVectorDecodeBHist ledger)
                          (bitVectorDecodeBHist provenance))
                  | _ :: _ => none

private theorem BitVectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BitVectorUp, bitVectorFromEventFlow (bitVectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk width spine ledger provenance =>
      change
        some
          (BitVectorUp.mk
            (bitVectorDecodeBHist (bitVectorEncodeBHist width))
            (bitVectorDecodeBHist (bitVectorEncodeBHist spine))
            (bitVectorDecodeBHist (bitVectorEncodeBHist ledger))
            (bitVectorDecodeBHist (bitVectorEncodeBHist provenance))) =
          some (BitVectorUp.mk width spine ledger provenance)
      rw [BitVectorTasteGate_single_carrier_alignment_decode_encode width,
        BitVectorTasteGate_single_carrier_alignment_decode_encode spine,
        BitVectorTasteGate_single_carrier_alignment_decode_encode ledger,
        BitVectorTasteGate_single_carrier_alignment_decode_encode provenance]

private theorem BitVectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BitVectorUp} :
    bitVectorToEventFlow x = bitVectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x = bitVectorFromEventFlow (bitVectorToEventFlow x) :=
        (BitVectorTasteGate_single_carrier_alignment_round_trip x).symm
      _ = bitVectorFromEventFlow (bitVectorToEventFlow y) :=
        congrArg bitVectorFromEventFlow heq
      _ = some y := BitVectorTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem BitVectorTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BitVectorUp, bitVectorFields x = bitVectorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk width₁ spine₁ ledger₁ provenance₁ =>
      cases y with
      | mk width₂ spine₂ ledger₂ provenance₂ =>
          injection hfields with hwidth tail0
          injection tail0 with hspine tail1
          injection tail1 with hledger tail2
          injection tail2 with hprovenance _
          subst hwidth
          subst hspine
          subst hledger
          subst hprovenance
          rfl

instance bitVectorBHistCarrier : BHistCarrier BitVectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bitVectorToEventFlow
  fromEventFlow := bitVectorFromEventFlow

instance bitVectorChapterTasteGate : ChapterTasteGate BitVectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bitVectorFromEventFlow (bitVectorToEventFlow x) = some x
    exact BitVectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BitVectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bitVectorFieldFaithful : FieldFaithful BitVectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bitVectorFields
  field_faithful := BitVectorTasteGate_single_carrier_alignment_field_faithful

instance bitVectorNontrivial : Nontrivial BitVectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BitVectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BitVectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BitVectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bitVectorChapterTasteGate

theorem BitVectorTasteGate_single_carrier_alignment :
    (∀ h : BHist, bitVectorDecodeBHist (bitVectorEncodeBHist h) = h) ∧
      (∀ x : BitVectorUp, bitVectorFromEventFlow (bitVectorToEventFlow x) = some x) ∧
        (∀ x y : BitVectorUp, bitVectorToEventFlow x = bitVectorToEventFlow y → x = y) ∧
          bitVectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact BitVectorTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact BitVectorTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BitVectorTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.BitVectorUp
