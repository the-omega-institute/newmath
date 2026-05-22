import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedLinearOperatorUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedLinearOperatorUp : Type where
  | mk
      (source target action bound ledger linearity normBound metricTransport algebraRows
        refusal : BHist) : BoundedLinearOperatorUp
  deriving DecidableEq

def boundedLinearOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedLinearOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedLinearOperatorEncodeBHist h

def boundedLinearOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedLinearOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedLinearOperatorDecodeBHist tail)

private theorem boundedLinearOperatorDecode_encode_bhist :
    ∀ h : BHist, boundedLinearOperatorDecodeBHist
      (boundedLinearOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedLinearOperatorFields : BoundedLinearOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedLinearOperatorUp.mk source target action bound ledger linearity normBound
      metricTransport algebraRows refusal =>
      [source, target, action, bound, ledger, linearity, normBound, metricTransport,
        algebraRows, refusal]

def boundedLinearOperatorToEventFlow : BoundedLinearOperatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedLinearOperatorFields x).map boundedLinearOperatorEncodeBHist

def boundedLinearOperatorFromEventFlow : EventFlow → Option BoundedLinearOperatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | source :: target :: action :: bound :: ledger :: linearity :: normBound ::
      metricTransport :: algebraRows :: refusal :: [] =>
      some
        (BoundedLinearOperatorUp.mk
          (boundedLinearOperatorDecodeBHist source)
          (boundedLinearOperatorDecodeBHist target)
          (boundedLinearOperatorDecodeBHist action)
          (boundedLinearOperatorDecodeBHist bound)
          (boundedLinearOperatorDecodeBHist ledger)
          (boundedLinearOperatorDecodeBHist linearity)
          (boundedLinearOperatorDecodeBHist normBound)
          (boundedLinearOperatorDecodeBHist metricTransport)
          (boundedLinearOperatorDecodeBHist algebraRows)
          (boundedLinearOperatorDecodeBHist refusal))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k ::
      _rest => none

private theorem boundedLinearOperator_round_trip :
    ∀ x : BoundedLinearOperatorUp,
      boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target action bound ledger linearity normBound metricTransport algebraRows
      refusal =>
      change
        some
          (BoundedLinearOperatorUp.mk
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist source))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist target))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist action))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist bound))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist ledger))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist linearity))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist normBound))
            (boundedLinearOperatorDecodeBHist
              (boundedLinearOperatorEncodeBHist metricTransport))
            (boundedLinearOperatorDecodeBHist
              (boundedLinearOperatorEncodeBHist algebraRows))
            (boundedLinearOperatorDecodeBHist (boundedLinearOperatorEncodeBHist refusal))) =
          some
            (BoundedLinearOperatorUp.mk source target action bound ledger linearity normBound
              metricTransport algebraRows refusal)
      rw [boundedLinearOperatorDecode_encode_bhist source,
        boundedLinearOperatorDecode_encode_bhist target,
        boundedLinearOperatorDecode_encode_bhist action,
        boundedLinearOperatorDecode_encode_bhist bound,
        boundedLinearOperatorDecode_encode_bhist ledger,
        boundedLinearOperatorDecode_encode_bhist linearity,
        boundedLinearOperatorDecode_encode_bhist normBound,
        boundedLinearOperatorDecode_encode_bhist metricTransport,
        boundedLinearOperatorDecode_encode_bhist algebraRows,
        boundedLinearOperatorDecode_encode_bhist refusal]

private theorem boundedLinearOperatorToEventFlow_injective {x y : BoundedLinearOperatorUp} :
    boundedLinearOperatorToEventFlow x = boundedLinearOperatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) =
        boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow y) :=
    congrArg boundedLinearOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedLinearOperator_round_trip x).symm
      (Eq.trans hread (boundedLinearOperator_round_trip y)))

private theorem boundedLinearOperator_fields_faithful :
    ∀ x y : BoundedLinearOperatorUp,
      boundedLinearOperatorFields x = boundedLinearOperatorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source target action bound ledger linearity normBound metricTransport algebraRows
      refusal =>
      cases y with
      | mk source' target' action' bound' ledger' linearity' normBound' metricTransport'
          algebraRows' refusal' =>
          cases hfields
          rfl

instance boundedLinearOperatorBHistCarrier : BHistCarrier BoundedLinearOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedLinearOperatorToEventFlow
  fromEventFlow := boundedLinearOperatorFromEventFlow

instance boundedLinearOperatorChapterTasteGate : ChapterTasteGate BoundedLinearOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) = some x
    exact boundedLinearOperator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedLinearOperatorToEventFlow_injective heq)

instance boundedLinearOperatorFieldFaithful : FieldFaithful BoundedLinearOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedLinearOperatorFields
  field_faithful := boundedLinearOperator_fields_faithful

instance boundedLinearOperatorNontrivial : Nontrivial BoundedLinearOperatorUp where
  witness_pair :=
    ⟨BoundedLinearOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedLinearOperatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedLinearOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedLinearOperatorChapterTasteGate

theorem BoundedLinearOperatorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedLinearOperatorUp) ∧
      Nonempty (FieldFaithful BoundedLinearOperatorUp) ∧
      Nonempty (Nontrivial BoundedLinearOperatorUp) ∧
      (∀ h : BHist, boundedLinearOperatorDecodeBHist
        (boundedLinearOperatorEncodeBHist h) = h) ∧
      (∀ x : BoundedLinearOperatorUp,
        boundedLinearOperatorFromEventFlow (boundedLinearOperatorToEventFlow x) = some x) ∧
      (∀ x y : BoundedLinearOperatorUp,
        boundedLinearOperatorToEventFlow x = boundedLinearOperatorToEventFlow y → x = y) ∧
      boundedLinearOperatorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨⟨boundedLinearOperatorChapterTasteGate⟩, ⟨boundedLinearOperatorFieldFaithful⟩,
    ⟨boundedLinearOperatorNontrivial⟩, boundedLinearOperatorDecode_encode_bhist,
    boundedLinearOperator_round_trip,
    fun _ _ heq => boundedLinearOperatorToEventFlow_injective heq, rfl⟩

end BEDC.Derived.BoundedLinearOperatorUp.TasteGate
