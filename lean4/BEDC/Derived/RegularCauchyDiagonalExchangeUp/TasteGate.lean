import BEDC.Derived.RegularCauchyDiagonalExchangeUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalExchangeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def regularCauchyDiagonalExchangeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalExchangeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalExchangeEncodeBHist h

def regularCauchyDiagonalExchangeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalExchangeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalExchangeDecodeBHist tail)

private theorem regularCauchyDiagonalExchangeDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyDiagonalExchangeDecodeBHist
        (regularCauchyDiagonalExchangeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDiagonalExchangeFields :
    _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp.mk S D R Q T L H C P N =>
      [S, D, R, Q, T, L, H, C, P, N]

def regularCauchyDiagonalExchangeToEventFlow :
    _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyDiagonalExchangeFields x).map
        regularCauchyDiagonalExchangeEncodeBHist

private def regularCauchyDiagonalExchangeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDiagonalExchangeEventAt index rest

def regularCauchyDiagonalExchangeFromEventFlow :
    EventFlow → Option _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (_root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp.mk
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 0 ef))
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 1 ef))
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 2 ef))
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 3 ef))
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 4 ef))
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 5 ef))
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 6 ef))
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 7 ef))
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 8 ef))
        (regularCauchyDiagonalExchangeDecodeBHist
          (regularCauchyDiagonalExchangeEventAt 9 ef)))

private theorem regularCauchyDiagonalExchange_round_trip
    (x : _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp) :
    regularCauchyDiagonalExchangeFromEventFlow
        (regularCauchyDiagonalExchangeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S D R Q T L H C P N =>
      change
        some
          (_root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp.mk
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist S))
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist D))
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist R))
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist Q))
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist T))
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist L))
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist H))
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist C))
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist P))
            (regularCauchyDiagonalExchangeDecodeBHist
              (regularCauchyDiagonalExchangeEncodeBHist N))) =
          some (_root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp.mk
            S D R Q T L H C P N)
      rw [
        regularCauchyDiagonalExchangeDecode_encode_bhist S,
        regularCauchyDiagonalExchangeDecode_encode_bhist D,
        regularCauchyDiagonalExchangeDecode_encode_bhist R,
        regularCauchyDiagonalExchangeDecode_encode_bhist Q,
        regularCauchyDiagonalExchangeDecode_encode_bhist T,
        regularCauchyDiagonalExchangeDecode_encode_bhist L,
        regularCauchyDiagonalExchangeDecode_encode_bhist H,
        regularCauchyDiagonalExchangeDecode_encode_bhist C,
        regularCauchyDiagonalExchangeDecode_encode_bhist P,
        regularCauchyDiagonalExchangeDecode_encode_bhist N]

private theorem regularCauchyDiagonalExchangeToEventFlow_injective
    {x y : _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp} :
    regularCauchyDiagonalExchangeToEventFlow x =
        regularCauchyDiagonalExchangeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDiagonalExchangeFromEventFlow
          (regularCauchyDiagonalExchangeToEventFlow x) =
        regularCauchyDiagonalExchangeFromEventFlow
          (regularCauchyDiagonalExchangeToEventFlow y) :=
    congrArg regularCauchyDiagonalExchangeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (regularCauchyDiagonalExchange_round_trip x).symm
      (Eq.trans hread
        (regularCauchyDiagonalExchange_round_trip y)))

theorem RegularCauchyDiagonalExchangeFieldFaithfulConcrete :
    ∀ x y : _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp,
      regularCauchyDiagonalExchangeFields x =
          regularCauchyDiagonalExchangeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  intro x y hfields
  cases x with
  | mk S D R Q T L H C P N =>
      cases y with
      | mk S' D' R' Q' T' L' H' C' P' N' =>
          cases hfields
          rfl

instance regularCauchyDiagonalExchangeBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalExchangeToEventFlow
  fromEventFlow := regularCauchyDiagonalExchangeFromEventFlow

instance regularCauchyDiagonalExchangeChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalExchangeFromEventFlow
          (regularCauchyDiagonalExchangeToEventFlow x) = some x
    exact regularCauchyDiagonalExchange_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDiagonalExchangeToEventFlow_injective heq)

instance regularCauchyDiagonalExchangeFieldFaithful :
    FieldFaithful _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp where
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  fields := regularCauchyDiagonalExchangeFields
  field_faithful := RegularCauchyDiagonalExchangeFieldFaithfulConcrete

instance regularCauchyDiagonalExchangeNontrivial :
    Nontrivial _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨_root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate :
    ChapterTasteGate _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDiagonalExchangeChapterTasteGate

theorem RegularCauchyDiagonalExchangeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyDiagonalExchangeDecodeBHist
        (regularCauchyDiagonalExchangeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp) ∧
        Nonempty
          (ChapterTasteGate _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp) ∧
          Nonempty
            (FieldFaithful _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp) ∧
            Nonempty
              (Nontrivial _root_.BEDC.Derived.RegularCauchyDiagonalExchangeUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨regularCauchyDiagonalExchangeDecode_encode_bhist,
      ⟨regularCauchyDiagonalExchangeBHistCarrier⟩,
      ⟨regularCauchyDiagonalExchangeChapterTasteGate⟩,
      ⟨regularCauchyDiagonalExchangeFieldFaithful⟩,
      ⟨regularCauchyDiagonalExchangeNontrivial⟩⟩

end BEDC.Derived.RegularCauchyDiagonalExchangeUp
