import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLimitSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLimitSelectorUp : Type where
  | mk (A W D R E H C P N : BHist) : RegularCauchyLimitSelectorUp
  deriving DecidableEq

def regularCauchyLimitSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLimitSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLimitSelectorEncodeBHist h

def regularCauchyLimitSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLimitSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLimitSelectorDecodeBHist tail)

private theorem regularCauchyLimitSelectorDecodeEncodeBHist :
    ∀ h : BHist,
      regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLimitSelectorFields :
    RegularCauchyLimitSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLimitSelectorUp.mk A W D R E H C P N =>
      [A, W, D, R, E, H, C, P, N]

def regularCauchyLimitSelectorToEventFlow :
    RegularCauchyLimitSelectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyLimitSelectorFields x).map
      regularCauchyLimitSelectorEncodeBHist

private def regularCauchyLimitSelectorEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyLimitSelectorEventAtDefault index rest

def regularCauchyLimitSelectorFromEventFlow
    (ef : EventFlow) : Option RegularCauchyLimitSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyLimitSelectorUp.mk
      (regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEventAtDefault 0 ef))
      (regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEventAtDefault 1 ef))
      (regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEventAtDefault 2 ef))
      (regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEventAtDefault 3 ef))
      (regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEventAtDefault 4 ef))
      (regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEventAtDefault 5 ef))
      (regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEventAtDefault 6 ef))
      (regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEventAtDefault 7 ef))
      (regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEventAtDefault 8 ef)))

private theorem regularCauchyLimitSelectorRoundTrip :
    ∀ x : RegularCauchyLimitSelectorUp,
      regularCauchyLimitSelectorFromEventFlow
        (regularCauchyLimitSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W D R E H C P N =>
      change
        some
          (RegularCauchyLimitSelectorUp.mk
            (regularCauchyLimitSelectorDecodeBHist
              (regularCauchyLimitSelectorEncodeBHist A))
            (regularCauchyLimitSelectorDecodeBHist
              (regularCauchyLimitSelectorEncodeBHist W))
            (regularCauchyLimitSelectorDecodeBHist
              (regularCauchyLimitSelectorEncodeBHist D))
            (regularCauchyLimitSelectorDecodeBHist
              (regularCauchyLimitSelectorEncodeBHist R))
            (regularCauchyLimitSelectorDecodeBHist
              (regularCauchyLimitSelectorEncodeBHist E))
            (regularCauchyLimitSelectorDecodeBHist
              (regularCauchyLimitSelectorEncodeBHist H))
            (regularCauchyLimitSelectorDecodeBHist
              (regularCauchyLimitSelectorEncodeBHist C))
            (regularCauchyLimitSelectorDecodeBHist
              (regularCauchyLimitSelectorEncodeBHist P))
            (regularCauchyLimitSelectorDecodeBHist
              (regularCauchyLimitSelectorEncodeBHist N))) =
          some (RegularCauchyLimitSelectorUp.mk A W D R E H C P N)
      rw [regularCauchyLimitSelectorDecodeEncodeBHist A,
        regularCauchyLimitSelectorDecodeEncodeBHist W,
        regularCauchyLimitSelectorDecodeEncodeBHist D,
        regularCauchyLimitSelectorDecodeEncodeBHist R,
        regularCauchyLimitSelectorDecodeEncodeBHist E,
        regularCauchyLimitSelectorDecodeEncodeBHist H,
        regularCauchyLimitSelectorDecodeEncodeBHist C,
        regularCauchyLimitSelectorDecodeEncodeBHist P,
        regularCauchyLimitSelectorDecodeEncodeBHist N]

private theorem regularCauchyLimitSelectorToEventFlow_injective
    {x y : RegularCauchyLimitSelectorUp} :
    regularCauchyLimitSelectorToEventFlow x =
      regularCauchyLimitSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLimitSelectorFromEventFlow
          (regularCauchyLimitSelectorToEventFlow x) =
        regularCauchyLimitSelectorFromEventFlow
          (regularCauchyLimitSelectorToEventFlow y) :=
    congrArg regularCauchyLimitSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLimitSelectorRoundTrip x).symm
      (Eq.trans hread (regularCauchyLimitSelectorRoundTrip y)))

instance regularCauchyLimitSelectorBHistCarrier :
    BHistCarrier RegularCauchyLimitSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLimitSelectorToEventFlow
  fromEventFlow := regularCauchyLimitSelectorFromEventFlow

instance regularCauchyLimitSelectorChapterTasteGate :
    ChapterTasteGate RegularCauchyLimitSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLimitSelectorFromEventFlow
        (regularCauchyLimitSelectorToEventFlow x) = some x
    exact regularCauchyLimitSelectorRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLimitSelectorToEventFlow_injective heq)

instance regularCauchyLimitSelectorFieldFaithful :
    FieldFaithful RegularCauchyLimitSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyLimitSelectorFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk A1 W1 D1 R1 E1 H1 C1 P1 N1 =>
        cases y with
        | mk A2 W2 D2 R2 E2 H2 C2 P2 N2 =>
            cases hfields
            rfl

instance regularCauchyLimitSelectorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyLimitSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyLimitSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyLimitSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyLimitSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLimitSelectorChapterTasteGate

theorem RegularCauchyLimitSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyLimitSelectorDecodeBHist
        (regularCauchyLimitSelectorEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyLimitSelectorUp,
        regularCauchyLimitSelectorFromEventFlow
          (regularCauchyLimitSelectorToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyLimitSelectorUp,
        regularCauchyLimitSelectorToEventFlow x =
          regularCauchyLimitSelectorToEventFlow y -> x = y) ∧
      regularCauchyLimitSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyLimitSelectorDecodeEncodeBHist
  · constructor
    · exact regularCauchyLimitSelectorRoundTrip
    · constructor
      · intro x y heq
        exact regularCauchyLimitSelectorToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyLimitSelectorUp
