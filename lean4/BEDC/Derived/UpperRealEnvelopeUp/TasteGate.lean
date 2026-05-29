import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpperRealEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpperRealEnvelopeUp : Type where
  | mk (U L D S R A H C P N : BHist) : UpperRealEnvelopeUp
  deriving DecidableEq

def upperRealEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: upperRealEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: upperRealEnvelopeEncodeBHist h

def upperRealEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (upperRealEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (upperRealEnvelopeDecodeBHist tail)

private theorem upperRealEnvelope_decode_encode_bhist :
    ∀ h : BHist, upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def upperRealEnvelopeFields : UpperRealEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UpperRealEnvelopeUp.mk U L D S R A H C P N => [U, L, D, S, R, A, H, C, P, N]

def upperRealEnvelopeToEventFlow : UpperRealEnvelopeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (upperRealEnvelopeFields x).map upperRealEnvelopeEncodeBHist

private def upperRealEnvelopeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => upperRealEnvelopeEventAtDefault index rest

def upperRealEnvelopeFromEventFlow (ef : EventFlow) : Option UpperRealEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UpperRealEnvelopeUp.mk
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 0 ef))
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 1 ef))
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 2 ef))
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 3 ef))
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 4 ef))
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 5 ef))
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 6 ef))
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 7 ef))
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 8 ef))
      (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEventAtDefault 9 ef)))

private theorem upperRealEnvelope_round_trip :
    ∀ x : UpperRealEnvelopeUp,
      upperRealEnvelopeFromEventFlow (upperRealEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U L D S R A H C P N =>
      change
        some
          (UpperRealEnvelopeUp.mk
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist U))
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist L))
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist D))
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist S))
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist R))
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist A))
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist H))
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist C))
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist P))
            (upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist N))) =
          some (UpperRealEnvelopeUp.mk U L D S R A H C P N)
      rw [upperRealEnvelope_decode_encode_bhist U, upperRealEnvelope_decode_encode_bhist L,
        upperRealEnvelope_decode_encode_bhist D, upperRealEnvelope_decode_encode_bhist S,
        upperRealEnvelope_decode_encode_bhist R, upperRealEnvelope_decode_encode_bhist A,
        upperRealEnvelope_decode_encode_bhist H, upperRealEnvelope_decode_encode_bhist C,
        upperRealEnvelope_decode_encode_bhist P, upperRealEnvelope_decode_encode_bhist N]

private theorem upperRealEnvelopeToEventFlow_injective {x y : UpperRealEnvelopeUp} :
    upperRealEnvelopeToEventFlow x = upperRealEnvelopeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = upperRealEnvelopeFromEventFlow (upperRealEnvelopeToEventFlow x) :=
        (upperRealEnvelope_round_trip x).symm
      _ = upperRealEnvelopeFromEventFlow (upperRealEnvelopeToEventFlow y) :=
        congrArg upperRealEnvelopeFromEventFlow hxy
      _ = some y := upperRealEnvelope_round_trip y
  exact Option.some.inj optionEq

private theorem upperRealEnvelope_fields_faithful :
    ∀ x y : UpperRealEnvelopeUp, upperRealEnvelopeFields x = upperRealEnvelopeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 L1 D1 S1 R1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 L2 D2 S2 R2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance upperRealEnvelopeBHistCarrier : BHistCarrier UpperRealEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := upperRealEnvelopeToEventFlow
  fromEventFlow := upperRealEnvelopeFromEventFlow

instance upperRealEnvelopeChapterTasteGate : ChapterTasteGate UpperRealEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change upperRealEnvelopeFromEventFlow (upperRealEnvelopeToEventFlow x) = some x
    exact upperRealEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (upperRealEnvelopeToEventFlow_injective heq)

instance upperRealEnvelopeFieldFaithful : FieldFaithful UpperRealEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := upperRealEnvelopeFields
  field_faithful := upperRealEnvelope_fields_faithful

instance upperRealEnvelopeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial UpperRealEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UpperRealEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UpperRealEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UpperRealEnvelopeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UpperRealEnvelopeUp) ∧
      Nonempty (FieldFaithful UpperRealEnvelopeUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial UpperRealEnvelopeUp) ∧
          (∀ h : BHist, upperRealEnvelopeDecodeBHist (upperRealEnvelopeEncodeBHist h) = h) ∧
            (∀ x : UpperRealEnvelopeUp,
              upperRealEnvelopeFromEventFlow (upperRealEnvelopeToEventFlow x) = some x) ∧
              (∀ x y : UpperRealEnvelopeUp,
                upperRealEnvelopeToEventFlow x = upperRealEnvelopeToEventFlow y → x = y) ∧
                upperRealEnvelopeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨upperRealEnvelopeChapterTasteGate⟩,
      ⟨upperRealEnvelopeFieldFaithful⟩,
      ⟨upperRealEnvelopeNontrivial⟩,
      upperRealEnvelope_decode_encode_bhist,
      upperRealEnvelope_round_trip,
      (by
        intro x y heq
        exact upperRealEnvelopeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UpperRealEnvelopeUp
