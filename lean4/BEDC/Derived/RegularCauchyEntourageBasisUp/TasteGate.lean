import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyEntourageBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyEntourageBasisUp : Type where
  | mk (R W D B E H C P N : BHist) : RegularCauchyEntourageBasisUp
  deriving DecidableEq

def regularCauchyEntourageBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyEntourageBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyEntourageBasisEncodeBHist h

def regularCauchyEntourageBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyEntourageBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyEntourageBasisDecodeBHist tail)

private theorem regularCauchyEntourageBasisDecode_encode :
    ∀ h : BHist,
      regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyEntourageBasisFields :
    RegularCauchyEntourageBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyEntourageBasisUp.mk R W D B E H C P N => [R, W, D, B, E, H, C, P, N]

def regularCauchyEntourageBasisToEventFlow :
    RegularCauchyEntourageBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyEntourageBasisFields x).map regularCauchyEntourageBasisEncodeBHist

private def regularCauchyEntourageBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyEntourageBasisEventAtDefault index rest

def regularCauchyEntourageBasisFromEventFlow
    (ef : EventFlow) : Option RegularCauchyEntourageBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyEntourageBasisUp.mk
      (regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEventAtDefault 0 ef))
      (regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEventAtDefault 1 ef))
      (regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEventAtDefault 2 ef))
      (regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEventAtDefault 3 ef))
      (regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEventAtDefault 4 ef))
      (regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEventAtDefault 5 ef))
      (regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEventAtDefault 6 ef))
      (regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEventAtDefault 7 ef))
      (regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEventAtDefault 8 ef)))

private theorem regularCauchyEntourageBasis_round_trip :
    ∀ x : RegularCauchyEntourageBasisUp,
      regularCauchyEntourageBasisFromEventFlow
        (regularCauchyEntourageBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D B E H C P N =>
      change
        some
          (RegularCauchyEntourageBasisUp.mk
            (regularCauchyEntourageBasisDecodeBHist
              (regularCauchyEntourageBasisEncodeBHist R))
            (regularCauchyEntourageBasisDecodeBHist
              (regularCauchyEntourageBasisEncodeBHist W))
            (regularCauchyEntourageBasisDecodeBHist
              (regularCauchyEntourageBasisEncodeBHist D))
            (regularCauchyEntourageBasisDecodeBHist
              (regularCauchyEntourageBasisEncodeBHist B))
            (regularCauchyEntourageBasisDecodeBHist
              (regularCauchyEntourageBasisEncodeBHist E))
            (regularCauchyEntourageBasisDecodeBHist
              (regularCauchyEntourageBasisEncodeBHist H))
            (regularCauchyEntourageBasisDecodeBHist
              (regularCauchyEntourageBasisEncodeBHist C))
            (regularCauchyEntourageBasisDecodeBHist
              (regularCauchyEntourageBasisEncodeBHist P))
            (regularCauchyEntourageBasisDecodeBHist
              (regularCauchyEntourageBasisEncodeBHist N))) =
          some (RegularCauchyEntourageBasisUp.mk R W D B E H C P N)
      rw [regularCauchyEntourageBasisDecode_encode R]
      rw [regularCauchyEntourageBasisDecode_encode W]
      rw [regularCauchyEntourageBasisDecode_encode D]
      rw [regularCauchyEntourageBasisDecode_encode B]
      rw [regularCauchyEntourageBasisDecode_encode E]
      rw [regularCauchyEntourageBasisDecode_encode H]
      rw [regularCauchyEntourageBasisDecode_encode C]
      rw [regularCauchyEntourageBasisDecode_encode P]
      rw [regularCauchyEntourageBasisDecode_encode N]

private theorem regularCauchyEntourageBasisToEventFlow_injective
    {x y : RegularCauchyEntourageBasisUp} :
    regularCauchyEntourageBasisToEventFlow x =
      regularCauchyEntourageBasisToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyEntourageBasisFromEventFlow
          (regularCauchyEntourageBasisToEventFlow x) =
        regularCauchyEntourageBasisFromEventFlow
          (regularCauchyEntourageBasisToEventFlow y) :=
    congrArg regularCauchyEntourageBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyEntourageBasis_round_trip x).symm
      (Eq.trans hread (regularCauchyEntourageBasis_round_trip y)))

instance regularCauchyEntourageBasisBHistCarrier :
    BHistCarrier RegularCauchyEntourageBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyEntourageBasisToEventFlow
  fromEventFlow := regularCauchyEntourageBasisFromEventFlow

instance regularCauchyEntourageBasisChapterTasteGate :
    ChapterTasteGate RegularCauchyEntourageBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyEntourageBasisFromEventFlow
        (regularCauchyEntourageBasisToEventFlow x) = some x
    exact regularCauchyEntourageBasis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyEntourageBasisToEventFlow_injective heq)

theorem RegularCauchyEntourageBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyEntourageBasisDecodeBHist
        (regularCauchyEntourageBasisEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyEntourageBasisUp,
        regularCauchyEntourageBasisFromEventFlow
          (regularCauchyEntourageBasisToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyEntourageBasisUp,
        regularCauchyEntourageBasisToEventFlow x =
          regularCauchyEntourageBasisToEventFlow y → x = y) ∧
      regularCauchyEntourageBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyEntourageBasisDecode_encode,
      regularCauchyEntourageBasis_round_trip,
      fun _ _ heq => regularCauchyEntourageBasisToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyEntourageBasisUp
