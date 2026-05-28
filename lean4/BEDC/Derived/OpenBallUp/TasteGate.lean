import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OpenBallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OpenBallUp : Type where
  | mk (M C R X D B H Q P N : BHist) : OpenBallUp
  deriving DecidableEq

def openBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: openBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: openBallEncodeBHist h

def openBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (openBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (openBallDecodeBHist tail)

private theorem openBall_decode_encode_bhist :
    ∀ h : BHist, openBallDecodeBHist (openBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def openBallToEventFlow : OpenBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OpenBallUp.mk M C R X D B H Q P N =>
      [openBallEncodeBHist M,
        openBallEncodeBHist C,
        openBallEncodeBHist R,
        openBallEncodeBHist X,
        openBallEncodeBHist D,
        openBallEncodeBHist B,
        openBallEncodeBHist H,
        openBallEncodeBHist Q,
        openBallEncodeBHist P,
        openBallEncodeBHist N]

private def openBallRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => openBallRawAt n rest

private def openBallLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => openBallLengthEq n rest

def openBallFromEventFlow : EventFlow → Option OpenBallUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match openBallLengthEq 10 flow with
      | true =>
          some
            (OpenBallUp.mk
              (openBallDecodeBHist (openBallRawAt 0 flow))
              (openBallDecodeBHist (openBallRawAt 1 flow))
              (openBallDecodeBHist (openBallRawAt 2 flow))
              (openBallDecodeBHist (openBallRawAt 3 flow))
              (openBallDecodeBHist (openBallRawAt 4 flow))
              (openBallDecodeBHist (openBallRawAt 5 flow))
              (openBallDecodeBHist (openBallRawAt 6 flow))
              (openBallDecodeBHist (openBallRawAt 7 flow))
              (openBallDecodeBHist (openBallRawAt 8 flow))
              (openBallDecodeBHist (openBallRawAt 9 flow)))
      | false => none

private theorem openBall_round_trip :
    ∀ x : OpenBallUp,
      openBallFromEventFlow (openBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M C R X D B H Q P N =>
      change
        some
          (OpenBallUp.mk
            (openBallDecodeBHist (openBallEncodeBHist M))
            (openBallDecodeBHist (openBallEncodeBHist C))
            (openBallDecodeBHist (openBallEncodeBHist R))
            (openBallDecodeBHist (openBallEncodeBHist X))
            (openBallDecodeBHist (openBallEncodeBHist D))
            (openBallDecodeBHist (openBallEncodeBHist B))
            (openBallDecodeBHist (openBallEncodeBHist H))
            (openBallDecodeBHist (openBallEncodeBHist Q))
            (openBallDecodeBHist (openBallEncodeBHist P))
            (openBallDecodeBHist (openBallEncodeBHist N))) =
          some (OpenBallUp.mk M C R X D B H Q P N)
      rw [openBall_decode_encode_bhist M,
        openBall_decode_encode_bhist C,
        openBall_decode_encode_bhist R,
        openBall_decode_encode_bhist X,
        openBall_decode_encode_bhist D,
        openBall_decode_encode_bhist B,
        openBall_decode_encode_bhist H,
        openBall_decode_encode_bhist Q,
        openBall_decode_encode_bhist P,
        openBall_decode_encode_bhist N]

private theorem openBallToEventFlow_injective {x y : OpenBallUp} :
    openBallToEventFlow x = openBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      openBallFromEventFlow (openBallToEventFlow x) =
        openBallFromEventFlow (openBallToEventFlow y) :=
    congrArg openBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (openBall_round_trip x).symm
      (Eq.trans hread (openBall_round_trip y)))

instance openBallBHistCarrier : BHistCarrier OpenBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := openBallToEventFlow
  fromEventFlow := openBallFromEventFlow

instance openBallChapterTasteGate : ChapterTasteGate OpenBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change openBallFromEventFlow (openBallToEventFlow x) = some x
    exact openBall_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (openBallToEventFlow_injective heq)

def taste_gate : ChapterTasteGate OpenBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  openBallChapterTasteGate

theorem OpenBallTasteGate_single_carrier_alignment :
    (∀ h : BHist, openBallDecodeBHist (openBallEncodeBHist h) = h) ∧
      (∀ x : OpenBallUp,
        openBallFromEventFlow (openBallToEventFlow x) = some x) ∧
        (∀ x y : OpenBallUp,
          openBallToEventFlow x = openBallToEventFlow y → x = y) ∧
          openBallEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨openBall_decode_encode_bhist,
      openBall_round_trip,
      by
        intro x y heq
        exact openBallToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.OpenBallUp
