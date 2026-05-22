import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedLinearOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedLinearOperatorUp : Type where
  | mk (source target endpointAction bound ledger transport replay provenance nameCert :
      BHist) : BoundedLinearOperatorUp
  deriving DecidableEq

def boundedLinearOperatorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedLinearOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedLinearOperatorEncodeBHist h

def boundedLinearOperatorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedLinearOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedLinearOperatorDecodeBHist tail)

private theorem BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def boundedLinearOperatorFields : BoundedLinearOperatorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedLinearOperatorUp.mk source target endpointAction bound ledger transport replay
      provenance nameCert =>
      [source, target, endpointAction, bound, ledger, transport, replay, provenance, nameCert]

def boundedLinearOperatorToEventFlow : BoundedLinearOperatorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedLinearOperatorFields x).map boundedLinearOperatorEncodeBHist

private def boundedLinearOperatorEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedLinearOperatorEventAtDefault index rest

def boundedLinearOperatorFromEventFlow (ef : EventFlow) : Option BoundedLinearOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedLinearOperatorUp.mk
      (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEventAtDefault 0 ef))
      (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEventAtDefault 1 ef))
      (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEventAtDefault 2 ef))
      (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEventAtDefault 3 ef))
      (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEventAtDefault 4 ef))
      (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEventAtDefault 5 ef))
      (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEventAtDefault 6 ef))
      (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEventAtDefault 7 ef))
      (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEventAtDefault 8 ef)))

private theorem BoundedLinearOperatorUpTasteGate_single_carrier_alignment_round_trip :
    forall x : BoundedLinearOperatorUp,
      boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target endpointAction bound ledger transport replay provenance nameCert =>
      change
        some
          (BoundedLinearOperatorUp.mk
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist source))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist target))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist endpointAction))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist bound))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist ledger))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist transport))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist replay))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist provenance))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist nameCert))) =
          some
            (BoundedLinearOperatorUp.mk source target endpointAction bound ledger transport replay
              provenance nameCert)
      rw [BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode source,
        BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode target,
        BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode endpointAction,
        BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode bound,
        BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode ledger,
        BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode transport,
        BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode replay,
        BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode provenance,
        BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode nameCert]

private theorem BoundedLinearOperatorUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedLinearOperatorUp} :
    boundedLinearOperatorToEventFlow x = boundedLinearOperatorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) =
        boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow y) :=
    congrArg boundedLinearOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedLinearOperatorUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedLinearOperatorUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedLinearOperatorUpTasteGate_single_carrier_alignment_fields :
    forall x y : BoundedLinearOperatorUp,
      boundedLinearOperatorFields x = boundedLinearOperatorFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source target endpointAction bound ledger transport replay provenance nameCert =>
      cases y with
      | mk source' target' endpointAction' bound' ledger' transport' replay' provenance'
          nameCert' =>
          cases hfields
          rfl

instance boundedLinearOperatorBHistCarrier : BHistCarrier BoundedLinearOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedLinearOperatorToEventFlow
  fromEventFlow := boundedLinearOperatorFromEventFlow

instance boundedLinearOperatorChapterTasteGate :
    ChapterTasteGate BoundedLinearOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) = some x
    exact BoundedLinearOperatorUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedLinearOperatorUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedLinearOperatorFieldFaithful :
    FieldFaithful BoundedLinearOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedLinearOperatorFields
  field_faithful := BoundedLinearOperatorUpTasteGate_single_carrier_alignment_fields

instance boundedLinearOperatorNontrivial :
    Nontrivial BoundedLinearOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedLinearOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedLinearOperatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BoundedLinearOperatorUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedLinearOperatorUp) ∧ Nonempty (FieldFaithful BoundedLinearOperatorUp) ∧ Nonempty (BEDC.Meta.TasteGate.Nontrivial BoundedLinearOperatorUp) ∧ (∀ h : BHist, boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist h) = h) ∧ (∀ x : BoundedLinearOperatorUp, boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) = some x) ∧ (∀ x y : BoundedLinearOperatorUp, boundedLinearOperatorToEventFlow x = boundedLinearOperatorToEventFlow y → x = y) ∧ boundedLinearOperatorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨boundedLinearOperatorChapterTasteGate⟩,
      ⟨boundedLinearOperatorFieldFaithful⟩,
      ⟨boundedLinearOperatorNontrivial⟩,
      BoundedLinearOperatorUpTasteGate_single_carrier_alignment_decode,
      BoundedLinearOperatorUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BoundedLinearOperatorUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedLinearOperatorUp
