import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedSelfAdjointOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedSelfAdjointOperatorUp : Type where
  | mk (H I G N J S R T C P L : BHist) : BoundedSelfAdjointOperatorUp
  deriving DecidableEq

def boundedSelfAdjointOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedSelfAdjointOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedSelfAdjointOperatorEncodeBHist h

def boundedSelfAdjointOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedSelfAdjointOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedSelfAdjointOperatorDecodeBHist tail)

private theorem boundedSelfAdjointOperator_decode_encode_bhist :
    ∀ h : BHist,
      boundedSelfAdjointOperatorDecodeBHist
        (boundedSelfAdjointOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedSelfAdjointOperatorFields : BoundedSelfAdjointOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedSelfAdjointOperatorUp.mk H I G N J S R T C P L =>
      [H, I, G, N, J, S, R, T, C, P, L]

def boundedSelfAdjointOperatorToEventFlow :
    BoundedSelfAdjointOperatorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (boundedSelfAdjointOperatorFields x).map
    boundedSelfAdjointOperatorEncodeBHist

private def boundedSelfAdjointOperatorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedSelfAdjointOperatorEventAtDefault index rest

def boundedSelfAdjointOperatorFromEventFlow
    (ef : EventFlow) : Option BoundedSelfAdjointOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedSelfAdjointOperatorUp.mk
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 0 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 1 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 2 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 3 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 4 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 5 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 6 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 7 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 8 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 9 ef))
      (boundedSelfAdjointOperatorDecodeBHist (boundedSelfAdjointOperatorEventAtDefault 10 ef)))

private theorem boundedSelfAdjointOperator_round_trip :
    ∀ x : BoundedSelfAdjointOperatorUp,
      boundedSelfAdjointOperatorFromEventFlow
        (boundedSelfAdjointOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H I G N J S R T C P L =>
      change
        some
          (BoundedSelfAdjointOperatorUp.mk
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist H))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist I))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist G))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist N))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist J))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist S))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist R))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist T))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist C))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist P))
            (boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist L))) =
          some (BoundedSelfAdjointOperatorUp.mk H I G N J S R T C P L)
      rw [boundedSelfAdjointOperator_decode_encode_bhist H,
        boundedSelfAdjointOperator_decode_encode_bhist I,
        boundedSelfAdjointOperator_decode_encode_bhist G,
        boundedSelfAdjointOperator_decode_encode_bhist N,
        boundedSelfAdjointOperator_decode_encode_bhist J,
        boundedSelfAdjointOperator_decode_encode_bhist S,
        boundedSelfAdjointOperator_decode_encode_bhist R,
        boundedSelfAdjointOperator_decode_encode_bhist T,
        boundedSelfAdjointOperator_decode_encode_bhist C,
        boundedSelfAdjointOperator_decode_encode_bhist P,
        boundedSelfAdjointOperator_decode_encode_bhist L]

private theorem boundedSelfAdjointOperatorToEventFlow_injective
    {x y : BoundedSelfAdjointOperatorUp} :
    boundedSelfAdjointOperatorToEventFlow x =
      boundedSelfAdjointOperatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          boundedSelfAdjointOperatorFromEventFlow
            (boundedSelfAdjointOperatorToEventFlow x) :=
        (boundedSelfAdjointOperator_round_trip x).symm
      _ =
          boundedSelfAdjointOperatorFromEventFlow
            (boundedSelfAdjointOperatorToEventFlow y) :=
        congrArg boundedSelfAdjointOperatorFromEventFlow hxy
      _ = some y := boundedSelfAdjointOperator_round_trip y
  exact Option.some.inj optionEq

private theorem boundedSelfAdjointOperator_fields_faithful :
    ∀ x y : BoundedSelfAdjointOperatorUp,
      boundedSelfAdjointOperatorFields x =
        boundedSelfAdjointOperatorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H1 I1 G1 N1 J1 S1 R1 T1 C1 P1 L1 =>
      cases y with
      | mk H2 I2 G2 N2 J2 S2 R2 T2 C2 P2 L2 =>
          cases hfields
          rfl

instance boundedSelfAdjointOperatorBHistCarrier :
    BHistCarrier BoundedSelfAdjointOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedSelfAdjointOperatorToEventFlow
  fromEventFlow := boundedSelfAdjointOperatorFromEventFlow

instance boundedSelfAdjointOperatorChapterTasteGate :
    ChapterTasteGate BoundedSelfAdjointOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedSelfAdjointOperatorFromEventFlow
        (boundedSelfAdjointOperatorToEventFlow x) = some x
    exact boundedSelfAdjointOperator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedSelfAdjointOperatorToEventFlow_injective heq)

instance boundedSelfAdjointOperatorFieldFaithful :
    FieldFaithful BoundedSelfAdjointOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedSelfAdjointOperatorFields
  field_faithful := boundedSelfAdjointOperator_fields_faithful

instance boundedSelfAdjointOperatorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BoundedSelfAdjointOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedSelfAdjointOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedSelfAdjointOperatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem BoundedSelfAdjointOperatorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedSelfAdjointOperatorUp) ∧
      Nonempty (FieldFaithful BoundedSelfAdjointOperatorUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BoundedSelfAdjointOperatorUp) ∧
          (∀ h : BHist,
            boundedSelfAdjointOperatorDecodeBHist
              (boundedSelfAdjointOperatorEncodeBHist h) = h) ∧
            (∀ x : BoundedSelfAdjointOperatorUp,
              boundedSelfAdjointOperatorFromEventFlow
                (boundedSelfAdjointOperatorToEventFlow x) = some x) ∧
              (∀ x y : BoundedSelfAdjointOperatorUp,
                boundedSelfAdjointOperatorToEventFlow x =
                  boundedSelfAdjointOperatorToEventFlow y → x = y) ∧
                boundedSelfAdjointOperatorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨boundedSelfAdjointOperatorChapterTasteGate⟩,
      ⟨boundedSelfAdjointOperatorFieldFaithful⟩,
      ⟨boundedSelfAdjointOperatorNontrivial⟩,
      boundedSelfAdjointOperator_decode_encode_bhist,
      boundedSelfAdjointOperator_round_trip,
      (by
        intro x y heq
        exact boundedSelfAdjointOperatorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BoundedSelfAdjointOperatorUp
