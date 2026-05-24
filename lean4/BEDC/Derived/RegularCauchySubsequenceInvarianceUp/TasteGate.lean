import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubsequenceInvarianceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubsequenceInvarianceUp : Type where
  | mk (Q F S R D E H C P N : BHist) : RegularCauchySubsequenceInvarianceUp
  deriving DecidableEq

def regularCauchySubsequenceInvarianceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubsequenceInvarianceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubsequenceInvarianceEncodeBHist h

def regularCauchySubsequenceInvarianceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubsequenceInvarianceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubsequenceInvarianceDecodeBHist tail)

private theorem regularCauchySubsequenceInvariance_decode_encode :
    ∀ h : BHist,
      regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySubsequenceInvarianceFields :
    RegularCauchySubsequenceInvarianceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubsequenceInvarianceUp.mk Q F S R D E H C P N =>
      [Q, F, S, R, D, E, H, C, P, N]

def regularCauchySubsequenceInvarianceToEventFlow :
    RegularCauchySubsequenceInvarianceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchySubsequenceInvarianceFields x).map
        regularCauchySubsequenceInvarianceEncodeBHist

private def regularCauchySubsequenceInvarianceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySubsequenceInvarianceEventAt index rest

def regularCauchySubsequenceInvarianceFromEventFlow
    (ef : EventFlow) : Option RegularCauchySubsequenceInvarianceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySubsequenceInvarianceUp.mk
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 0 ef))
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 1 ef))
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 2 ef))
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 3 ef))
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 4 ef))
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 5 ef))
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 6 ef))
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 7 ef))
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 8 ef))
      (regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEventAt 9 ef)))

private theorem regularCauchySubsequenceInvariance_round_trip
    (x : RegularCauchySubsequenceInvarianceUp) :
    regularCauchySubsequenceInvarianceFromEventFlow
        (regularCauchySubsequenceInvarianceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q F S R D E H C P N =>
      change
        some
          (RegularCauchySubsequenceInvarianceUp.mk
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist Q))
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist F))
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist S))
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist R))
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist D))
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist E))
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist H))
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist C))
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist P))
            (regularCauchySubsequenceInvarianceDecodeBHist
              (regularCauchySubsequenceInvarianceEncodeBHist N))) =
          some (RegularCauchySubsequenceInvarianceUp.mk Q F S R D E H C P N)
      rw [regularCauchySubsequenceInvariance_decode_encode Q,
        regularCauchySubsequenceInvariance_decode_encode F,
        regularCauchySubsequenceInvariance_decode_encode S,
        regularCauchySubsequenceInvariance_decode_encode R,
        regularCauchySubsequenceInvariance_decode_encode D,
        regularCauchySubsequenceInvariance_decode_encode E,
        regularCauchySubsequenceInvariance_decode_encode H,
        regularCauchySubsequenceInvariance_decode_encode C,
        regularCauchySubsequenceInvariance_decode_encode P,
        regularCauchySubsequenceInvariance_decode_encode N]

private theorem regularCauchySubsequenceInvarianceToEventFlow_injective
    {x y : RegularCauchySubsequenceInvarianceUp} :
    regularCauchySubsequenceInvarianceToEventFlow x =
        regularCauchySubsequenceInvarianceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubsequenceInvarianceFromEventFlow
          (regularCauchySubsequenceInvarianceToEventFlow x) =
        regularCauchySubsequenceInvarianceFromEventFlow
          (regularCauchySubsequenceInvarianceToEventFlow y) :=
    congrArg regularCauchySubsequenceInvarianceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySubsequenceInvariance_round_trip x).symm
      (Eq.trans hread (regularCauchySubsequenceInvariance_round_trip y)))

instance regularCauchySubsequenceInvarianceBHistCarrier :
    BHistCarrier RegularCauchySubsequenceInvarianceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubsequenceInvarianceToEventFlow
  fromEventFlow := regularCauchySubsequenceInvarianceFromEventFlow

instance regularCauchySubsequenceInvarianceChapterTasteGate :
    ChapterTasteGate RegularCauchySubsequenceInvarianceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubsequenceInvarianceFromEventFlow
          (regularCauchySubsequenceInvarianceToEventFlow x) =
        some x
    exact regularCauchySubsequenceInvariance_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySubsequenceInvarianceToEventFlow_injective heq)

def RegularCauchySubsequenceInvarianceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchySubsequenceInvarianceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySubsequenceInvarianceChapterTasteGate

theorem RegularCauchySubsequenceInvarianceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySubsequenceInvarianceDecodeBHist
        (regularCauchySubsequenceInvarianceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchySubsequenceInvarianceUp) ∧
        Nonempty (ChapterTasteGate RegularCauchySubsequenceInvarianceUp) ∧
          regularCauchySubsequenceInvarianceEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchySubsequenceInvariance_decode_encode,
      Nonempty.intro regularCauchySubsequenceInvarianceBHistCarrier,
      Nonempty.intro regularCauchySubsequenceInvarianceChapterTasteGate,
      rfl⟩

end BEDC.Derived.RegularCauchySubsequenceInvarianceUp
