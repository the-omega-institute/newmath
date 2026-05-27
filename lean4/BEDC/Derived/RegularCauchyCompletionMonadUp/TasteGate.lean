import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionMonadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionMonadUp : Type where
  | mk (W R D U B E H C P N : BHist) : RegularCauchyCompletionMonadUp
  deriving DecidableEq

def regularCauchyCompletionMonadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionMonadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionMonadEncodeBHist h

def regularCauchyCompletionMonadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionMonadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionMonadDecodeBHist tail)

private theorem regularCauchyCompletionMonad_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyCompletionMonadDecodeBHist
        (regularCauchyCompletionMonadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyCompletionMonadFields :
    RegularCauchyCompletionMonadUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionMonadUp.mk W R D U B E H C P N =>
      [W, R, D, U, B, E, H, C, P, N]

def regularCauchyCompletionMonadToEventFlow :
    RegularCauchyCompletionMonadUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyCompletionMonadFields x).map regularCauchyCompletionMonadEncodeBHist

private def regularCauchyCompletionMonadRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyCompletionMonadRawAt n rest

private def regularCauchyCompletionMonadLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyCompletionMonadLengthEq n rest

def regularCauchyCompletionMonadFromEventFlow :
    EventFlow → Option RegularCauchyCompletionMonadUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyCompletionMonadLengthEq 10 flow with
      | true =>
          some
            (RegularCauchyCompletionMonadUp.mk
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 0 flow))
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 1 flow))
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 2 flow))
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 3 flow))
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 4 flow))
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 5 flow))
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 6 flow))
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 7 flow))
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 8 flow))
              (regularCauchyCompletionMonadDecodeBHist
                (regularCauchyCompletionMonadRawAt 9 flow)))
      | false => none

private theorem regularCauchyCompletionMonad_round_trip :
    ∀ x : RegularCauchyCompletionMonadUp,
      regularCauchyCompletionMonadFromEventFlow
        (regularCauchyCompletionMonadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W R D U B E H C P N =>
      change
        some
          (RegularCauchyCompletionMonadUp.mk
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist W))
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist R))
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist D))
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist U))
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist B))
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist E))
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist H))
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist C))
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist P))
            (regularCauchyCompletionMonadDecodeBHist
              (regularCauchyCompletionMonadEncodeBHist N))) =
          some (RegularCauchyCompletionMonadUp.mk W R D U B E H C P N)
      rw [regularCauchyCompletionMonad_decode_encode_bhist W,
        regularCauchyCompletionMonad_decode_encode_bhist R,
        regularCauchyCompletionMonad_decode_encode_bhist D,
        regularCauchyCompletionMonad_decode_encode_bhist U,
        regularCauchyCompletionMonad_decode_encode_bhist B,
        regularCauchyCompletionMonad_decode_encode_bhist E,
        regularCauchyCompletionMonad_decode_encode_bhist H,
        regularCauchyCompletionMonad_decode_encode_bhist C,
        regularCauchyCompletionMonad_decode_encode_bhist P,
        regularCauchyCompletionMonad_decode_encode_bhist N]

private theorem regularCauchyCompletionMonadToEventFlow_injective
    {x y : RegularCauchyCompletionMonadUp} :
    regularCauchyCompletionMonadToEventFlow x =
      regularCauchyCompletionMonadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionMonadFromEventFlow
          (regularCauchyCompletionMonadToEventFlow x) =
        regularCauchyCompletionMonadFromEventFlow
          (regularCauchyCompletionMonadToEventFlow y) :=
    congrArg regularCauchyCompletionMonadFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCompletionMonad_round_trip x).symm
      (Eq.trans hread (regularCauchyCompletionMonad_round_trip y)))

instance regularCauchyCompletionMonadBHistCarrier :
    BHistCarrier RegularCauchyCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionMonadToEventFlow
  fromEventFlow := regularCauchyCompletionMonadFromEventFlow

instance regularCauchyCompletionMonadChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionMonadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionMonadFromEventFlow
        (regularCauchyCompletionMonadToEventFlow x) = some x
    exact regularCauchyCompletionMonad_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCompletionMonadToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyCompletionMonadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompletionMonadChapterTasteGate

theorem RegularCauchyCompletionMonadTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCompletionMonadDecodeBHist
        (regularCauchyCompletionMonadEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCompletionMonadUp,
        regularCauchyCompletionMonadFromEventFlow
          (regularCauchyCompletionMonadToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyCompletionMonadUp,
          regularCauchyCompletionMonadToEventFlow x =
            regularCauchyCompletionMonadToEventFlow y → x = y) ∧
          regularCauchyCompletionMonadEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyCompletionMonad_decode_encode_bhist,
      regularCauchyCompletionMonad_round_trip,
      fun _ _ heq => regularCauchyCompletionMonadToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyCompletionMonadUp
