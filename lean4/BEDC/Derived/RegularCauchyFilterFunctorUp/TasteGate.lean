import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFilterFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFilterFunctorUp : Type where
  | mk (I B W D R E A H C P N : BHist) : RegularCauchyFilterFunctorUp

def regularCauchyFilterFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFilterFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFilterFunctorEncodeBHist h

def regularCauchyFilterFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFilterFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFilterFunctorDecodeBHist tail)

private theorem RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFilterFunctorToEventFlow :
    RegularCauchyFilterFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterFunctorUp.mk I B W D R E A H C P N =>
      [[BMark.b1, BMark.b0, BMark.b0],
        regularCauchyFilterFunctorEncodeBHist I,
        [BMark.b1, BMark.b0, BMark.b1],
        regularCauchyFilterFunctorEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyFilterFunctorEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyFilterFunctorEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyFilterFunctorEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyFilterFunctorEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyFilterFunctorEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyFilterFunctorEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyFilterFunctorEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyFilterFunctorEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyFilterFunctorEncodeBHist N]

private def regularCauchyFilterFunctorEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyFilterFunctorEventAtDefault index rest

def regularCauchyFilterFunctorFromEventFlow
    (ef : EventFlow) : Option RegularCauchyFilterFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyFilterFunctorUp.mk
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 1 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 3 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 5 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 7 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 9 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 11 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 13 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 15 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 17 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 19 ef))
      (regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEventAtDefault 21 ef)))

private theorem RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyFilterFunctorUp,
      regularCauchyFilterFunctorFromEventFlow
        (regularCauchyFilterFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I B W D R E A H C P N =>
      change
        some
          (RegularCauchyFilterFunctorUp.mk
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist I))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist B))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist W))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist D))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist R))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist E))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist A))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist H))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist C))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist P))
            (regularCauchyFilterFunctorDecodeBHist
              (regularCauchyFilterFunctorEncodeBHist N))) =
          some (RegularCauchyFilterFunctorUp.mk I B W D R E A H C P N)
      rw [RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode I,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyFilterFunctorUp} :
    regularCauchyFilterFunctorToEventFlow x =
      regularCauchyFilterFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFilterFunctorFromEventFlow
          (regularCauchyFilterFunctorToEventFlow x) =
        regularCauchyFilterFunctorFromEventFlow
          (regularCauchyFilterFunctorToEventFlow y) :=
    congrArg regularCauchyFilterFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_round_trip y)))

def regularCauchyFilterFunctorFields :
    RegularCauchyFilterFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterFunctorUp.mk I B W D R E A H C P N =>
      [I, B, W, D, R, E, A, H, C, P, N]

private theorem RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyFilterFunctorUp,
      regularCauchyFilterFunctorFields x =
        regularCauchyFilterFunctorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 B1 W1 D1 R1 E1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 B2 W2 D2 R2 E2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyFilterFunctorBHistCarrier :
    BHistCarrier RegularCauchyFilterFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFilterFunctorToEventFlow
  fromEventFlow := regularCauchyFilterFunctorFromEventFlow

instance regularCauchyFilterFunctorChapterTasteGate :
    ChapterTasteGate RegularCauchyFilterFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyFilterFunctorFromEventFlow
        (regularCauchyFilterFunctorToEventFlow x) = some x
    exact RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyFilterFunctorFieldFaithful :
    FieldFaithful RegularCauchyFilterFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyFilterFunctorFields
  field_faithful := RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate RegularCauchyFilterFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyFilterFunctorChapterTasteGate

theorem RegularCauchyFilterFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyFilterFunctorDecodeBHist
        (regularCauchyFilterFunctorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyFilterFunctorUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyFilterFunctorUp) ∧
          regularCauchyFilterFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RegularCauchyFilterFunctorTasteGate_single_carrier_alignment_decode_encode,
      ⟨regularCauchyFilterFunctorBHistCarrier⟩,
      ⟨regularCauchyFilterFunctorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyFilterFunctorUp
