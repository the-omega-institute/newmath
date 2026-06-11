import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocatedLimitUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (window tolerance readback interval locator realSeal transport replay provenance
      localName : BHist) : RegularCauchyLocatedLimitUp
  deriving DecidableEq

def regularCauchyLocatedLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedLimitEncodeBHist h

def regularCauchyLocatedLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedLimitDecodeBHist tail)

private theorem regularCauchyLocatedLimit_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLocatedLimitFields :
    RegularCauchyLocatedLimitUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyLocatedLimitUp.mk window tolerance readback interval locator realSeal
      transport replay provenance localName =>
      [window, tolerance, readback, interval, locator, realSeal, transport, replay,
        provenance, localName]

def regularCauchyLocatedLimitToEventFlow :
    RegularCauchyLocatedLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyLocatedLimitFields x).map regularCauchyLocatedLimitEncodeBHist

private def regularCauchyLocatedLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyLocatedLimitEventAtDefault index rest

def regularCauchyLocatedLimitFromEventFlow :
    EventFlow → Option RegularCauchyLocatedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyLocatedLimitUp.mk
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 0 ef))
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 1 ef))
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 2 ef))
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 3 ef))
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 4 ef))
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 5 ef))
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 6 ef))
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 7 ef))
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 8 ef))
        (regularCauchyLocatedLimitDecodeBHist (regularCauchyLocatedLimitEventAtDefault 9 ef)))

private theorem regularCauchyLocatedLimit_round_trip :
    ∀ x : RegularCauchyLocatedLimitUp,
      regularCauchyLocatedLimitFromEventFlow
          (regularCauchyLocatedLimitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window tolerance readback interval locator realSeal transport replay provenance
      localName =>
      change
        some
          (RegularCauchyLocatedLimitUp.mk
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist window))
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist tolerance))
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist readback))
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist interval))
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist locator))
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist realSeal))
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist transport))
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist replay))
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist provenance))
            (regularCauchyLocatedLimitDecodeBHist
              (regularCauchyLocatedLimitEncodeBHist localName))) =
          some
            (RegularCauchyLocatedLimitUp.mk window tolerance readback interval locator realSeal
              transport replay provenance localName)
      rw [regularCauchyLocatedLimit_decode_encode_bhist window,
        regularCauchyLocatedLimit_decode_encode_bhist tolerance,
        regularCauchyLocatedLimit_decode_encode_bhist readback,
        regularCauchyLocatedLimit_decode_encode_bhist interval,
        regularCauchyLocatedLimit_decode_encode_bhist locator,
        regularCauchyLocatedLimit_decode_encode_bhist realSeal,
        regularCauchyLocatedLimit_decode_encode_bhist transport,
        regularCauchyLocatedLimit_decode_encode_bhist replay,
        regularCauchyLocatedLimit_decode_encode_bhist provenance,
        regularCauchyLocatedLimit_decode_encode_bhist localName]

private theorem regularCauchyLocatedLimitToEventFlow_injective
    {x y : RegularCauchyLocatedLimitUp} :
    regularCauchyLocatedLimitToEventFlow x =
        regularCauchyLocatedLimitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyLocatedLimitFromEventFlow
            (regularCauchyLocatedLimitToEventFlow x) :=
        (regularCauchyLocatedLimit_round_trip x).symm
      _ =
          regularCauchyLocatedLimitFromEventFlow
            (regularCauchyLocatedLimitToEventFlow y) :=
        congrArg regularCauchyLocatedLimitFromEventFlow hxy
      _ = some y := regularCauchyLocatedLimit_round_trip y
  exact Option.some.inj optionEq

instance regularCauchyLocatedLimitBHistCarrier :
    BHistCarrier RegularCauchyLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedLimitToEventFlow
  fromEventFlow := regularCauchyLocatedLimitFromEventFlow

instance regularCauchyLocatedLimitChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLocatedLimitFromEventFlow
          (regularCauchyLocatedLimitToEventFlow x) =
        some x
    exact regularCauchyLocatedLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLocatedLimitToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyLocatedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLocatedLimitChapterTasteGate

theorem RegularCauchyLocatedLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyLocatedLimitDecodeBHist
        (regularCauchyLocatedLimitEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyLocatedLimitUp,
        regularCauchyLocatedLimitFromEventFlow
          (regularCauchyLocatedLimitToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyLocatedLimitUp,
          regularCauchyLocatedLimitToEventFlow x =
              regularCauchyLocatedLimitToEventFlow y → x = y) ∧
          regularCauchyLocatedLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyLocatedLimit_decode_encode_bhist,
      regularCauchyLocatedLimit_round_trip,
      (fun _ _ heq => regularCauchyLocatedLimitToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyLocatedLimitUp
