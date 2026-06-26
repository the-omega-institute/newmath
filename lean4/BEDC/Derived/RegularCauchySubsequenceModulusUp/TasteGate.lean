import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubsequenceModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubsequenceModulusUp : Type where
  | mk (Q S D W R E H C P N : BHist) : RegularCauchySubsequenceModulusUp
  deriving DecidableEq

def regularCauchySubsequenceModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubsequenceModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubsequenceModulusEncodeBHist h

def regularCauchySubsequenceModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubsequenceModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubsequenceModulusDecodeBHist tail)

private theorem RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchySubsequenceModulusDecodeBHist
        (regularCauchySubsequenceModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySubsequenceModulusToEventFlow :
    RegularCauchySubsequenceModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubsequenceModulusUp.mk Q S D W R E H C P N =>
      [regularCauchySubsequenceModulusEncodeBHist Q,
        regularCauchySubsequenceModulusEncodeBHist S,
        regularCauchySubsequenceModulusEncodeBHist D,
        regularCauchySubsequenceModulusEncodeBHist W,
        regularCauchySubsequenceModulusEncodeBHist R,
        regularCauchySubsequenceModulusEncodeBHist E,
        regularCauchySubsequenceModulusEncodeBHist H,
        regularCauchySubsequenceModulusEncodeBHist C,
        regularCauchySubsequenceModulusEncodeBHist P,
        regularCauchySubsequenceModulusEncodeBHist N]

private def regularCauchySubsequenceModulusRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchySubsequenceModulusRawAt n rest

private def regularCauchySubsequenceModulusLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchySubsequenceModulusLengthEq n rest

def regularCauchySubsequenceModulusFromEventFlow :
    EventFlow → Option RegularCauchySubsequenceModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchySubsequenceModulusLengthEq 10 flow with
      | true =>
          some
            (RegularCauchySubsequenceModulusUp.mk
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 0 flow))
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 1 flow))
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 2 flow))
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 3 flow))
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 4 flow))
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 5 flow))
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 6 flow))
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 7 flow))
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 8 flow))
              (regularCauchySubsequenceModulusDecodeBHist
                (regularCauchySubsequenceModulusRawAt 9 flow)))
      | false => none

private theorem RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySubsequenceModulusUp,
      regularCauchySubsequenceModulusFromEventFlow
        (regularCauchySubsequenceModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S D W R E H C P N =>
      change
        some
          (RegularCauchySubsequenceModulusUp.mk
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist Q))
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist S))
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist D))
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist W))
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist R))
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist E))
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist H))
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist C))
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist P))
            (regularCauchySubsequenceModulusDecodeBHist
              (regularCauchySubsequenceModulusEncodeBHist N))) =
          some (RegularCauchySubsequenceModulusUp.mk Q S D W R E H C P N)
      rw [RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode Q,
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode S,
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode D,
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode W,
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode R,
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode E,
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode H,
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode C,
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode P,
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySubsequenceModulusUp} :
    regularCauchySubsequenceModulusToEventFlow x =
      regularCauchySubsequenceModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubsequenceModulusFromEventFlow
          (regularCauchySubsequenceModulusToEventFlow x) =
        regularCauchySubsequenceModulusFromEventFlow
          (regularCauchySubsequenceModulusToEventFlow y) :=
    congrArg regularCauchySubsequenceModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchySubsequenceModulusBHistCarrier :
    BHistCarrier RegularCauchySubsequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubsequenceModulusToEventFlow
  fromEventFlow := regularCauchySubsequenceModulusFromEventFlow

instance regularCauchySubsequenceModulusChapterTasteGate :
    ChapterTasteGate RegularCauchySubsequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubsequenceModulusFromEventFlow
          (regularCauchySubsequenceModulusToEventFlow x) =
        some x
    exact RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def regularCauchySubsequenceModulus_taste_gate :
    ChapterTasteGate RegularCauchySubsequenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySubsequenceModulusChapterTasteGate

theorem RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchySubsequenceModulusDecodeBHist
          (regularCauchySubsequenceModulusEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySubsequenceModulusUp,
        regularCauchySubsequenceModulusFromEventFlow
          (regularCauchySubsequenceModulusToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchySubsequenceModulusUp,
        regularCauchySubsequenceModulusToEventFlow x =
          regularCauchySubsequenceModulusToEventFlow y → x = y) ∧
      regularCauchySubsequenceModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_decode,
      RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        RegularCauchySubsequenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.RegularCauchySubsequenceModulusUp
