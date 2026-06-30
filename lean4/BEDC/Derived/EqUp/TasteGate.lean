import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EqUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EqUp : Type where
  | mk (anchor witness transport classifier provenance : BHist) : EqUp
  deriving DecidableEq

def eqEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eqEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eqEncodeBHist h

def eqDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eqDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eqDecodeBHist tail)

private theorem EqTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, eqDecodeBHist (eqEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eqFields : EqUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EqUp.mk anchor witness transport classifier provenance =>
      [anchor, witness, transport, classifier, provenance]

def eqToEventFlow : EqUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (eqFields x).map eqEncodeBHist

def eqEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eqEventAt index rest

def eqFromEventFlow (ef : EventFlow) : Option EqUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EqUp.mk
      (eqDecodeBHist (eqEventAt 0 ef))
      (eqDecodeBHist (eqEventAt 1 ef))
      (eqDecodeBHist (eqEventAt 2 ef))
      (eqDecodeBHist (eqEventAt 3 ef))
      (eqDecodeBHist (eqEventAt 4 ef)))

private theorem eq_round_trip :
    forall x : EqUp, eqFromEventFlow (eqToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk anchor witness transport classifier provenance =>
      change
        some
          (EqUp.mk
            (eqDecodeBHist (eqEncodeBHist anchor))
            (eqDecodeBHist (eqEncodeBHist witness))
            (eqDecodeBHist (eqEncodeBHist transport))
            (eqDecodeBHist (eqEncodeBHist classifier))
            (eqDecodeBHist (eqEncodeBHist provenance))) =
          some (EqUp.mk anchor witness transport classifier provenance)
      rw [EqTasteGate_single_carrier_alignment_decode_encode anchor,
        EqTasteGate_single_carrier_alignment_decode_encode witness,
        EqTasteGate_single_carrier_alignment_decode_encode transport,
        EqTasteGate_single_carrier_alignment_decode_encode classifier,
        EqTasteGate_single_carrier_alignment_decode_encode provenance]

private theorem eqToEventFlow_injective {x y : EqUp} :
    eqToEventFlow x = eqToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eqFromEventFlow (eqToEventFlow x) = eqFromEventFlow (eqToEventFlow y) :=
    congrArg eqFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (eq_round_trip x).symm (Eq.trans hread (eq_round_trip y)))

private theorem eq_field_faithful :
    forall x y : EqUp, eqFields x = eqFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk anchor₁ witness₁ transport₁ classifier₁ provenance₁ =>
      cases y with
      | mk anchor₂ witness₂ transport₂ classifier₂ provenance₂ =>
          cases hfields
          rfl

instance eqBHistCarrier : BHistCarrier EqUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eqToEventFlow
  fromEventFlow := eqFromEventFlow

instance eqChapterTasteGate : ChapterTasteGate EqUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => eq_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (eqToEventFlow_injective heq)

instance eqFieldFaithful : FieldFaithful EqUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eqFields
  field_faithful := eq_field_faithful

instance eqNontrivial : BEDC.Meta.TasteGate.Nontrivial EqUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EqUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EqUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def eqTasteGate : ChapterTasteGate EqUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eqChapterTasteGate

theorem EqTasteGate_single_carrier_alignment :
    (∀ h : BHist, eqDecodeBHist (eqEncodeBHist h) = h) ∧
      (∀ x : EqUp, eqFromEventFlow (eqToEventFlow x) = some x) ∧
        (∀ x y : EqUp, eqToEventFlow x = eqToEventFlow y → x = y) ∧
          eqEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact EqTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact eq_round_trip
    · constructor
      · intro x y heq
        exact eqToEventFlow_injective heq
      · rfl

end BEDC.Derived.EqUp
