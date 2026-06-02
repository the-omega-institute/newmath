import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocatedFieldUp : Type where
  | mk (S W D A M I Q E H C P N : BHist) : RegularCauchyLocatedFieldUp
  deriving DecidableEq

def regularCauchyLocatedFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedFieldEncodeBHist h

def regularCauchyLocatedFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedFieldDecodeBHist tail)

private theorem RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyLocatedFieldDecodeBHist
        (regularCauchyLocatedFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLocatedFieldToEventFlow :
    RegularCauchyLocatedFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocatedFieldUp.mk S W D A M I Q E H C P N =>
      [[BMark.b0],
        regularCauchyLocatedFieldEncodeBHist S,
        [BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyLocatedFieldEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedFieldEncodeBHist N]

private def regularCauchyLocatedFieldEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyLocatedFieldEventAtDefault index rest

def regularCauchyLocatedFieldFromEventFlow :
    EventFlow → Option RegularCauchyLocatedFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyLocatedFieldUp.mk
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 1 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 3 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 5 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 7 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 9 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 11 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 13 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 15 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 17 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 19 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 21 ef))
        (regularCauchyLocatedFieldDecodeBHist
          (regularCauchyLocatedFieldEventAtDefault 23 ef)))

private theorem RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyLocatedFieldUp,
      regularCauchyLocatedFieldFromEventFlow
        (regularCauchyLocatedFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D A M I Q E H C P N =>
      change
        some
          (RegularCauchyLocatedFieldUp.mk
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist S))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist W))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist D))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist A))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist M))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist I))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist Q))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist E))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist H))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist C))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist P))
            (regularCauchyLocatedFieldDecodeBHist
              (regularCauchyLocatedFieldEncodeBHist N))) =
          some (RegularCauchyLocatedFieldUp.mk S W D A M I Q E H C P N)
      rw [RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode S,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode W,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode D,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode A,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode M,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode I,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode E,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode H,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode C,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode P,
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyLocatedFieldUp} :
    regularCauchyLocatedFieldToEventFlow x =
      regularCauchyLocatedFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocatedFieldFromEventFlow
          (regularCauchyLocatedFieldToEventFlow x) =
        regularCauchyLocatedFieldFromEventFlow
          (regularCauchyLocatedFieldToEventFlow y) :=
    congrArg regularCauchyLocatedFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_round_trip y)))

private def regularCauchyLocatedFieldFields :
    RegularCauchyLocatedFieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocatedFieldUp.mk S W D A M I Q E H C P N =>
      [S, W, D, A, M, I, Q, E, H, C, P, N]

private theorem RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_fields :
    ∀ x y : RegularCauchyLocatedFieldUp,
      regularCauchyLocatedFieldFields x = regularCauchyLocatedFieldFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 W1 D1 A1 M1 I1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 D2 A2 M2 I2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyLocatedFieldBHistCarrier :
    BHistCarrier RegularCauchyLocatedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedFieldToEventFlow
  fromEventFlow := regularCauchyLocatedFieldFromEventFlow

instance regularCauchyLocatedFieldChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLocatedFieldFromEventFlow
        (regularCauchyLocatedFieldToEventFlow x) = some x
    exact RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_injective heq)

instance regularCauchyLocatedFieldFieldFaithful :
    FieldFaithful RegularCauchyLocatedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyLocatedFieldFields
  field_faithful := RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_fields

instance regularCauchyLocatedFieldNontrivial :
    Nontrivial RegularCauchyLocatedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyLocatedFieldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyLocatedFieldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyLocatedFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLocatedFieldChapterTasteGate

theorem RegularCauchyLocatedFieldTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyLocatedFieldDecodeBHist
        (regularCauchyLocatedFieldEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyLocatedFieldUp,
        regularCauchyLocatedFieldFromEventFlow
          (regularCauchyLocatedFieldToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyLocatedFieldUp,
          regularCauchyLocatedFieldToEventFlow x =
            regularCauchyLocatedFieldToEventFlow y → x = y) ∧
          regularCauchyLocatedFieldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_decode,
      RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyLocatedFieldTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyLocatedFieldUp
