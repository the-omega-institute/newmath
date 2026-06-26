import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionCounitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionCounitUp : Type where
  | mk (M U Q S R D E H C P N : BHist) : RegularCauchyCompletionCounitUp
  deriving DecidableEq

def regularCauchyCompletionCounitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionCounitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionCounitEncodeBHist h

def regularCauchyCompletionCounitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionCounitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionCounitDecodeBHist tail)

private theorem RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyCompletionCounitDecodeBHist
        (regularCauchyCompletionCounitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionCounitToEventFlow :
    RegularCauchyCompletionCounitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionCounitUp.mk M U Q S R D E H C P N =>
      [regularCauchyCompletionCounitEncodeBHist M,
        regularCauchyCompletionCounitEncodeBHist U,
        regularCauchyCompletionCounitEncodeBHist Q,
        regularCauchyCompletionCounitEncodeBHist S,
        regularCauchyCompletionCounitEncodeBHist R,
        regularCauchyCompletionCounitEncodeBHist D,
        regularCauchyCompletionCounitEncodeBHist E,
        regularCauchyCompletionCounitEncodeBHist H,
        regularCauchyCompletionCounitEncodeBHist C,
        regularCauchyCompletionCounitEncodeBHist P,
        regularCauchyCompletionCounitEncodeBHist N]

private def regularCauchyCompletionCounitRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyCompletionCounitRawAt n rest

private def regularCauchyCompletionCounitLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyCompletionCounitLengthEq n rest

def regularCauchyCompletionCounitFromEventFlow :
    EventFlow → Option RegularCauchyCompletionCounitUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyCompletionCounitLengthEq 11 flow with
      | true =>
          some
            (RegularCauchyCompletionCounitUp.mk
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 0 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 1 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 2 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 3 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 4 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 5 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 6 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 7 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 8 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 9 flow))
              (regularCauchyCompletionCounitDecodeBHist
                (regularCauchyCompletionCounitRawAt 10 flow)))
      | false => none

private theorem RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCompletionCounitUp,
      regularCauchyCompletionCounitFromEventFlow
        (regularCauchyCompletionCounitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M U Q S R D E H C P N =>
      change
        some
          (RegularCauchyCompletionCounitUp.mk
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist M))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist U))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist Q))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist S))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist R))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist D))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist E))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist H))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist C))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist P))
            (regularCauchyCompletionCounitDecodeBHist
              (regularCauchyCompletionCounitEncodeBHist N))) =
          some (RegularCauchyCompletionCounitUp.mk M U Q S R D E H C P N)
      rw [RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode M,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode U,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode S,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode R,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode D,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode E,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode H,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode C,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode P,
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCompletionCounitUp} :
    regularCauchyCompletionCounitToEventFlow x =
      regularCauchyCompletionCounitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionCounitFromEventFlow
          (regularCauchyCompletionCounitToEventFlow x) =
        regularCauchyCompletionCounitFromEventFlow
          (regularCauchyCompletionCounitToEventFlow y) :=
    congrArg regularCauchyCompletionCounitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyCompletionCounitBHistCarrier :
    BHistCarrier RegularCauchyCompletionCounitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionCounitToEventFlow
  fromEventFlow := regularCauchyCompletionCounitFromEventFlow

instance regularCauchyCompletionCounitChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionCounitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionCounitFromEventFlow
          (regularCauchyCompletionCounitToEventFlow x) =
        some x
    exact RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def regularCauchyCompletionCounit_taste_gate :
    ChapterTasteGate RegularCauchyCompletionCounitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompletionCounitChapterTasteGate

theorem RegularCauchyCompletionCounitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyCompletionCounitDecodeBHist
          (regularCauchyCompletionCounitEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCompletionCounitUp,
        regularCauchyCompletionCounitFromEventFlow
          (regularCauchyCompletionCounitToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyCompletionCounitUp,
        regularCauchyCompletionCounitToEventFlow x =
          regularCauchyCompletionCounitToEventFlow y → x = y) ∧
      regularCauchyCompletionCounitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_decode,
      RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        RegularCauchyCompletionCounitTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.RegularCauchyCompletionCounitUp
