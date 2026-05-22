import BEDC.Derived.AddUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AddUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AddUp : Type where
  | mk (source pattern classifier stability ledger : BHist) : AddUp
  deriving DecidableEq

def addUpEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: addUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: addUpEncodeBHist h

def addUpDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (addUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (addUpDecodeBHist tail)

private theorem AddUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist, addUpDecodeBHist (addUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def addUpFields : AddUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AddUp.mk source pattern classifier stability ledger =>
      [source, pattern, classifier, stability, ledger]

def addUpToEventFlow : AddUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (addUpFields x).map addUpEncodeBHist

def addUpEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => addUpEventAt index rest

def addUpFromEventFlow : EventFlow -> Option AddUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (AddUp.mk
          (addUpDecodeBHist (addUpEventAt 0 flow))
          (addUpDecodeBHist (addUpEventAt 1 flow))
          (addUpDecodeBHist (addUpEventAt 2 flow))
          (addUpDecodeBHist (addUpEventAt 3 flow))
          (addUpDecodeBHist (addUpEventAt 4 flow)))

private theorem AddUpTasteGate_single_carrier_alignment_round_trip :
    forall x : AddUp, addUpFromEventFlow (addUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source pattern classifier stability ledger =>
      change
        some
          (AddUp.mk
            (addUpDecodeBHist (addUpEncodeBHist source))
            (addUpDecodeBHist (addUpEncodeBHist pattern))
            (addUpDecodeBHist (addUpEncodeBHist classifier))
            (addUpDecodeBHist (addUpEncodeBHist stability))
            (addUpDecodeBHist (addUpEncodeBHist ledger))) =
          some (AddUp.mk source pattern classifier stability ledger)
      rw [AddUpTasteGate_single_carrier_alignment_decode source,
        AddUpTasteGate_single_carrier_alignment_decode pattern,
        AddUpTasteGate_single_carrier_alignment_decode classifier,
        AddUpTasteGate_single_carrier_alignment_decode stability,
        AddUpTasteGate_single_carrier_alignment_decode ledger]

private theorem addUpToEventFlow_injective {x y : AddUp} :
    addUpToEventFlow x = addUpToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      addUpFromEventFlow (addUpToEventFlow x) =
        addUpFromEventFlow (addUpToEventFlow y) :=
    congrArg addUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AddUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AddUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem AddUpTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : AddUp, addUpFields x = addUpFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source1 pattern1 classifier1 stability1 ledger1 =>
      cases y with
      | mk source2 pattern2 classifier2 stability2 ledger2 =>
          cases hfields
          rfl

instance addUpBHistCarrier : BHistCarrier AddUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := addUpToEventFlow
  fromEventFlow := addUpFromEventFlow

instance addUpChapterTasteGate : ChapterTasteGate AddUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change addUpFromEventFlow (addUpToEventFlow x) = some x
    exact AddUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (addUpToEventFlow_injective heq)

instance addUpFieldFaithful : FieldFaithful AddUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := addUpFields
  field_faithful := AddUpTasteGate_single_carrier_alignment_fields_faithful

instance addUpNontrivial : Nontrivial AddUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AddUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AddUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AddUp :=
  -- BEDC touchpoint anchor: BHist BMark
  addUpChapterTasteGate

theorem AddUpTasteGate_single_carrier_alignment :
    (forall x : AddUp, addUpFromEventFlow (addUpToEventFlow x) = some x) ∧
      (forall x y : AddUp, addUpToEventFlow x = addUpToEventFlow y -> x = y) ∧
        addUpFields
          (AddUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨AddUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => addUpToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AddUp
