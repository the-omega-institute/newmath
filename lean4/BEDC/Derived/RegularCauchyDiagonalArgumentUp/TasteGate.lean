import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalArgumentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDiagonalArgumentUp : Type where
  | mk (F W D R E H C P N : BHist) : RegularCauchyDiagonalArgumentUp
  deriving DecidableEq

private def regularCauchyDiagonalArgumentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalArgumentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalArgumentEncodeBHist h

private def regularCauchyDiagonalArgumentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalArgumentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalArgumentDecodeBHist tail)

private theorem regularCauchyDiagonalArgument_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyDiagonalArgumentDecodeBHist
        (regularCauchyDiagonalArgumentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def regularCauchyDiagonalArgumentToEventFlow :
    RegularCauchyDiagonalArgumentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDiagonalArgumentUp.mk F W D R E H C P N =>
      [regularCauchyDiagonalArgumentEncodeBHist F,
        regularCauchyDiagonalArgumentEncodeBHist W,
        regularCauchyDiagonalArgumentEncodeBHist D,
        regularCauchyDiagonalArgumentEncodeBHist R,
        regularCauchyDiagonalArgumentEncodeBHist E,
        regularCauchyDiagonalArgumentEncodeBHist H,
        regularCauchyDiagonalArgumentEncodeBHist C,
        regularCauchyDiagonalArgumentEncodeBHist P,
        regularCauchyDiagonalArgumentEncodeBHist N]

private def regularCauchyDiagonalArgumentRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyDiagonalArgumentRawAt n rest

private def regularCauchyDiagonalArgumentLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyDiagonalArgumentLengthEq n rest

private def regularCauchyDiagonalArgumentFromEventFlow :
    EventFlow → Option RegularCauchyDiagonalArgumentUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyDiagonalArgumentLengthEq 9 flow with
      | true =>
          some
            (RegularCauchyDiagonalArgumentUp.mk
              (regularCauchyDiagonalArgumentDecodeBHist
                (regularCauchyDiagonalArgumentRawAt 0 flow))
              (regularCauchyDiagonalArgumentDecodeBHist
                (regularCauchyDiagonalArgumentRawAt 1 flow))
              (regularCauchyDiagonalArgumentDecodeBHist
                (regularCauchyDiagonalArgumentRawAt 2 flow))
              (regularCauchyDiagonalArgumentDecodeBHist
                (regularCauchyDiagonalArgumentRawAt 3 flow))
              (regularCauchyDiagonalArgumentDecodeBHist
                (regularCauchyDiagonalArgumentRawAt 4 flow))
              (regularCauchyDiagonalArgumentDecodeBHist
                (regularCauchyDiagonalArgumentRawAt 5 flow))
              (regularCauchyDiagonalArgumentDecodeBHist
                (regularCauchyDiagonalArgumentRawAt 6 flow))
              (regularCauchyDiagonalArgumentDecodeBHist
                (regularCauchyDiagonalArgumentRawAt 7 flow))
              (regularCauchyDiagonalArgumentDecodeBHist
                (regularCauchyDiagonalArgumentRawAt 8 flow)))
      | false => none

private theorem regularCauchyDiagonalArgument_round_trip :
    ∀ x : RegularCauchyDiagonalArgumentUp,
      regularCauchyDiagonalArgumentFromEventFlow
        (regularCauchyDiagonalArgumentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F W D R E H C P N =>
      change
        some
          (RegularCauchyDiagonalArgumentUp.mk
            (regularCauchyDiagonalArgumentDecodeBHist
              (regularCauchyDiagonalArgumentEncodeBHist F))
            (regularCauchyDiagonalArgumentDecodeBHist
              (regularCauchyDiagonalArgumentEncodeBHist W))
            (regularCauchyDiagonalArgumentDecodeBHist
              (regularCauchyDiagonalArgumentEncodeBHist D))
            (regularCauchyDiagonalArgumentDecodeBHist
              (regularCauchyDiagonalArgumentEncodeBHist R))
            (regularCauchyDiagonalArgumentDecodeBHist
              (regularCauchyDiagonalArgumentEncodeBHist E))
            (regularCauchyDiagonalArgumentDecodeBHist
              (regularCauchyDiagonalArgumentEncodeBHist H))
            (regularCauchyDiagonalArgumentDecodeBHist
              (regularCauchyDiagonalArgumentEncodeBHist C))
            (regularCauchyDiagonalArgumentDecodeBHist
              (regularCauchyDiagonalArgumentEncodeBHist P))
            (regularCauchyDiagonalArgumentDecodeBHist
              (regularCauchyDiagonalArgumentEncodeBHist N))) =
          some (RegularCauchyDiagonalArgumentUp.mk F W D R E H C P N)
      rw [regularCauchyDiagonalArgument_decode_encode_bhist F,
        regularCauchyDiagonalArgument_decode_encode_bhist W,
        regularCauchyDiagonalArgument_decode_encode_bhist D,
        regularCauchyDiagonalArgument_decode_encode_bhist R,
        regularCauchyDiagonalArgument_decode_encode_bhist E,
        regularCauchyDiagonalArgument_decode_encode_bhist H,
        regularCauchyDiagonalArgument_decode_encode_bhist C,
        regularCauchyDiagonalArgument_decode_encode_bhist P,
        regularCauchyDiagonalArgument_decode_encode_bhist N]

private theorem regularCauchyDiagonalArgumentToEventFlow_injective
    {x y : RegularCauchyDiagonalArgumentUp} :
    regularCauchyDiagonalArgumentToEventFlow x =
        regularCauchyDiagonalArgumentToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDiagonalArgumentFromEventFlow
          (regularCauchyDiagonalArgumentToEventFlow x) =
        regularCauchyDiagonalArgumentFromEventFlow
          (regularCauchyDiagonalArgumentToEventFlow y) :=
    congrArg regularCauchyDiagonalArgumentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyDiagonalArgument_round_trip x).symm
      (Eq.trans hread (regularCauchyDiagonalArgument_round_trip y)))

instance regularCauchyDiagonalArgumentBHistCarrier :
    BHistCarrier RegularCauchyDiagonalArgumentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalArgumentToEventFlow
  fromEventFlow := regularCauchyDiagonalArgumentFromEventFlow

instance regularCauchyDiagonalArgumentChapterTasteGate :
    ChapterTasteGate RegularCauchyDiagonalArgumentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalArgumentFromEventFlow
        (regularCauchyDiagonalArgumentToEventFlow x) = some x
    exact regularCauchyDiagonalArgument_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDiagonalArgumentToEventFlow_injective heq)

theorem RegularCauchyDiagonalArgumentTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyDiagonalArgumentDecodeBHist
        (regularCauchyDiagonalArgumentEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyDiagonalArgumentUp,
        regularCauchyDiagonalArgumentFromEventFlow
          (regularCauchyDiagonalArgumentToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyDiagonalArgumentUp,
          regularCauchyDiagonalArgumentToEventFlow x =
              regularCauchyDiagonalArgumentToEventFlow y →
            x = y) ∧
          regularCauchyDiagonalArgumentEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyDiagonalArgument_decode_encode_bhist,
      regularCauchyDiagonalArgument_round_trip,
      by
        intro x y heq
        exact regularCauchyDiagonalArgumentToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyDiagonalArgumentUp
