import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTransformUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTransformUp : Type where
  | mk (S R M D U Q E H C P N : BHist) : RegularCauchyTransformUp
  deriving DecidableEq

def regularCauchyTransformEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTransformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTransformEncodeBHist h

def regularCauchyTransformDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTransformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTransformDecodeBHist tail)

private theorem regularCauchyTransform_decode_encode_bhist :
    forall h : BHist,
      regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTransformFields : RegularCauchyTransformUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTransformUp.mk S R M D U Q E H C P N =>
      [S, R, M, D, U, Q, E, H, C, P, N]

def regularCauchyTransformToEventFlow : RegularCauchyTransformUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTransformFields x).map regularCauchyTransformEncodeBHist

private def regularCauchyTransformEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTransformEventAtDefault index rest

def regularCauchyTransformFromEventFlow
    (ef : EventFlow) : Option RegularCauchyTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTransformUp.mk
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 0 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 1 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 2 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 3 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 4 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 5 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 6 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 7 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 8 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 9 ef))
      (regularCauchyTransformDecodeBHist (regularCauchyTransformEventAtDefault 10 ef)))

private theorem RegularCauchyTransformTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyTransformUp,
      regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R M D U Q E H C P N =>
      change
        some
          (RegularCauchyTransformUp.mk
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist S))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist R))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist M))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist D))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist U))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist Q))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist E))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist H))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist C))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist P))
            (regularCauchyTransformDecodeBHist (regularCauchyTransformEncodeBHist N))) =
          some (RegularCauchyTransformUp.mk S R M D U Q E H C P N)
      rw [regularCauchyTransform_decode_encode_bhist S,
        regularCauchyTransform_decode_encode_bhist R,
        regularCauchyTransform_decode_encode_bhist M,
        regularCauchyTransform_decode_encode_bhist D,
        regularCauchyTransform_decode_encode_bhist U,
        regularCauchyTransform_decode_encode_bhist Q,
        regularCauchyTransform_decode_encode_bhist E,
        regularCauchyTransform_decode_encode_bhist H,
        regularCauchyTransform_decode_encode_bhist C,
        regularCauchyTransform_decode_encode_bhist P,
        regularCauchyTransform_decode_encode_bhist N]

private theorem RegularCauchyTransformTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyTransformUp} :
    regularCauchyTransformToEventFlow x = regularCauchyTransformToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow x) =
        regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow y) :=
    congrArg regularCauchyTransformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyTransformTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyTransformTasteGate_single_carrier_alignment_round_trip y)))

private theorem regularCauchyTransform_fields_faithful :
    forall x y : RegularCauchyTransformUp,
      regularCauchyTransformFields x = regularCauchyTransformFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 M1 D1 U1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 M2 D2 U2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyTransformBHistCarrier : BHistCarrier RegularCauchyTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTransformToEventFlow
  fromEventFlow := regularCauchyTransformFromEventFlow

instance regularCauchyTransformChapterTasteGate : ChapterTasteGate RegularCauchyTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyTransformFromEventFlow (regularCauchyTransformToEventFlow x) =
      some x
    exact RegularCauchyTransformTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyTransformTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyTransformFieldFaithful : FieldFaithful RegularCauchyTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTransformFields
  field_faithful := regularCauchyTransform_fields_faithful

instance regularCauchyTransformNontrivial : Nontrivial RegularCauchyTransformUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTransformUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyTransformUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTransformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTransformChapterTasteGate

theorem RegularCauchyTransformTasteGate_single_carrier_alignment :
    exists x y : RegularCauchyTransformUp,
      x ≠ y ∧
        regularCauchyTransformFields x =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
          regularCauchyTransformEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  refine
    ⟨RegularCauchyTransformUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyTransformUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ?_, rfl, rfl⟩
  intro h
  cases h

end BEDC.Derived.RegularCauchyTransformUp
