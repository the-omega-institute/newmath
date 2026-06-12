import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyReflectionLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyReflectionLedgerUp : Type where
  | mk (Q W D R K U J H C P N : BHist) : RegularCauchyReflectionLedgerUp
  deriving DecidableEq

def regularCauchyReflectionLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyReflectionLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyReflectionLedgerEncodeBHist h

def regularCauchyReflectionLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyReflectionLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyReflectionLedgerDecodeBHist tail)

private theorem regularCauchyReflectionLedger_decode_encode :
    ∀ h : BHist,
      regularCauchyReflectionLedgerDecodeBHist
          (regularCauchyReflectionLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyReflectionLedgerFields :
    RegularCauchyReflectionLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyReflectionLedgerUp.mk Q W D R K U J H C P N =>
      [Q, W, D, R, K, U, J, H, C, P, N]

def regularCauchyReflectionLedgerToEventFlow :
    RegularCauchyReflectionLedgerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyReflectionLedgerFields x).map regularCauchyReflectionLedgerEncodeBHist

private def regularCauchyReflectionLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyReflectionLedgerEventAtDefault index rest

def regularCauchyReflectionLedgerFromEventFlow
    (ef : EventFlow) : Option RegularCauchyReflectionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyReflectionLedgerUp.mk
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 0 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 1 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 2 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 3 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 4 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 5 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 6 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 7 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 8 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 9 ef))
      (regularCauchyReflectionLedgerDecodeBHist
        (regularCauchyReflectionLedgerEventAtDefault 10 ef)))

private theorem regularCauchyReflectionLedger_round_trip :
    ∀ x : RegularCauchyReflectionLedgerUp,
      regularCauchyReflectionLedgerFromEventFlow
          (regularCauchyReflectionLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q W D R K U J H C P N =>
      change
        some
          (RegularCauchyReflectionLedgerUp.mk
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist Q))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist W))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist D))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist R))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist K))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist U))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist J))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist H))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist C))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist P))
            (regularCauchyReflectionLedgerDecodeBHist
              (regularCauchyReflectionLedgerEncodeBHist N))) =
          some (RegularCauchyReflectionLedgerUp.mk Q W D R K U J H C P N)
      rw [regularCauchyReflectionLedger_decode_encode Q,
        regularCauchyReflectionLedger_decode_encode W,
        regularCauchyReflectionLedger_decode_encode D,
        regularCauchyReflectionLedger_decode_encode R,
        regularCauchyReflectionLedger_decode_encode K,
        regularCauchyReflectionLedger_decode_encode U,
        regularCauchyReflectionLedger_decode_encode J,
        regularCauchyReflectionLedger_decode_encode H,
        regularCauchyReflectionLedger_decode_encode C,
        regularCauchyReflectionLedger_decode_encode P,
        regularCauchyReflectionLedger_decode_encode N]

private theorem regularCauchyReflectionLedgerToEventFlow_injective
    {x y : RegularCauchyReflectionLedgerUp} :
    regularCauchyReflectionLedgerToEventFlow x =
        regularCauchyReflectionLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyReflectionLedgerFromEventFlow
            (regularCauchyReflectionLedgerToEventFlow x) :=
        (regularCauchyReflectionLedger_round_trip x).symm
      _ =
          regularCauchyReflectionLedgerFromEventFlow
            (regularCauchyReflectionLedgerToEventFlow y) :=
        congrArg regularCauchyReflectionLedgerFromEventFlow hxy
      _ = some y := regularCauchyReflectionLedger_round_trip y
  exact Option.some.inj optionEq

private theorem regularCauchyReflectionLedger_fields_faithful :
    ∀ x y : RegularCauchyReflectionLedgerUp,
      regularCauchyReflectionLedgerFields x = regularCauchyReflectionLedgerFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 W1 D1 R1 K1 U1 J1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 W2 D2 R2 K2 U2 J2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyReflectionLedgerBHistCarrier :
    BHistCarrier RegularCauchyReflectionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyReflectionLedgerToEventFlow
  fromEventFlow := regularCauchyReflectionLedgerFromEventFlow

instance regularCauchyReflectionLedgerChapterTasteGate :
    ChapterTasteGate RegularCauchyReflectionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyReflectionLedgerFromEventFlow
          (regularCauchyReflectionLedgerToEventFlow x) =
        some x
    exact regularCauchyReflectionLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyReflectionLedgerToEventFlow_injective heq)

instance regularCauchyReflectionLedgerFieldFaithful :
    FieldFaithful RegularCauchyReflectionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyReflectionLedgerFields
  field_faithful := regularCauchyReflectionLedger_fields_faithful

instance regularCauchyReflectionLedgerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyReflectionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyReflectionLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyReflectionLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyReflectionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyReflectionLedgerChapterTasteGate

theorem RegularCauchyReflectionLedgerTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegularCauchyReflectionLedgerUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyReflectionLedgerUp) ∧
        Nonempty (FieldFaithful RegularCauchyReflectionLedgerUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyReflectionLedgerUp) ∧
            regularCauchyReflectionLedgerEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              regularCauchyReflectionLedgerEncodeBHist (BHist.e0 BHist.Empty) =
                [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyReflectionLedgerBHistCarrier⟩,
      ⟨regularCauchyReflectionLedgerChapterTasteGate⟩,
      ⟨regularCauchyReflectionLedgerFieldFaithful⟩,
      ⟨regularCauchyReflectionLedgerNontrivial⟩,
      rfl, rfl⟩

end BEDC.Derived.RegularCauchyReflectionLedgerUp
