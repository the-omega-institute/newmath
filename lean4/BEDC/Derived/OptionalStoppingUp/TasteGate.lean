import BEDC.Derived.OptionalStoppingUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OptionalStoppingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OptionalStoppingUp : Type where
  | mk (Omega X T b V F I H C P N : BHist) : OptionalStoppingUp
  deriving DecidableEq

def optionalStoppingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: optionalStoppingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: optionalStoppingEncodeBHist h

def optionalStoppingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (optionalStoppingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (optionalStoppingDecodeBHist tail)

private theorem optionalStopping_decode_encode :
    ∀ h : BHist, optionalStoppingDecodeBHist (optionalStoppingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def optionalStoppingFields : OptionalStoppingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OptionalStoppingUp.mk Omega X T b V F I H C P N =>
      [Omega, X, T, b, V, F, I, H, C, P, N]

def optionalStoppingToEventFlow : OptionalStoppingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (optionalStoppingFields x).map optionalStoppingEncodeBHist

private def optionalStoppingDecodePacket
    (Omega X T b V F I H C P N : RawEvent) : OptionalStoppingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  OptionalStoppingUp.mk
    (optionalStoppingDecodeBHist Omega)
    (optionalStoppingDecodeBHist X)
    (optionalStoppingDecodeBHist T)
    (optionalStoppingDecodeBHist b)
    (optionalStoppingDecodeBHist V)
    (optionalStoppingDecodeBHist F)
    (optionalStoppingDecodeBHist I)
    (optionalStoppingDecodeBHist H)
    (optionalStoppingDecodeBHist C)
    (optionalStoppingDecodeBHist P)
    (optionalStoppingDecodeBHist N)

private def optionalStoppingRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => optionalStoppingRawAt n rest

private def optionalStoppingLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => optionalStoppingLengthEq n rest

def optionalStoppingFromEventFlow (flow : EventFlow) : Option OptionalStoppingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match optionalStoppingLengthEq 11 flow with
  | true =>
      some
        (optionalStoppingDecodePacket
          (optionalStoppingRawAt 0 flow)
          (optionalStoppingRawAt 1 flow)
          (optionalStoppingRawAt 2 flow)
          (optionalStoppingRawAt 3 flow)
          (optionalStoppingRawAt 4 flow)
          (optionalStoppingRawAt 5 flow)
          (optionalStoppingRawAt 6 flow)
          (optionalStoppingRawAt 7 flow)
          (optionalStoppingRawAt 8 flow)
          (optionalStoppingRawAt 9 flow)
          (optionalStoppingRawAt 10 flow))
  | false => none

private theorem optionalStopping_round_trip :
    ∀ x : OptionalStoppingUp,
      optionalStoppingFromEventFlow (optionalStoppingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Omega X T b V F I H C P N =>
      change
        some
          (optionalStoppingDecodePacket
            (optionalStoppingEncodeBHist Omega)
            (optionalStoppingEncodeBHist X)
            (optionalStoppingEncodeBHist T)
            (optionalStoppingEncodeBHist b)
            (optionalStoppingEncodeBHist V)
            (optionalStoppingEncodeBHist F)
            (optionalStoppingEncodeBHist I)
            (optionalStoppingEncodeBHist H)
            (optionalStoppingEncodeBHist C)
            (optionalStoppingEncodeBHist P)
            (optionalStoppingEncodeBHist N)) =
          some (OptionalStoppingUp.mk Omega X T b V F I H C P N)
      unfold optionalStoppingDecodePacket
      rw [optionalStopping_decode_encode Omega,
        optionalStopping_decode_encode X,
        optionalStopping_decode_encode T,
        optionalStopping_decode_encode b,
        optionalStopping_decode_encode V,
        optionalStopping_decode_encode F,
        optionalStopping_decode_encode I,
        optionalStopping_decode_encode H,
        optionalStopping_decode_encode C,
        optionalStopping_decode_encode P,
        optionalStopping_decode_encode N]

private theorem optionalStoppingToEventFlow_injective {x y : OptionalStoppingUp} :
    optionalStoppingToEventFlow x = optionalStoppingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      optionalStoppingFromEventFlow (optionalStoppingToEventFlow x) =
        optionalStoppingFromEventFlow (optionalStoppingToEventFlow y) :=
    congrArg optionalStoppingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (optionalStopping_round_trip x).symm
      (Eq.trans hread (optionalStopping_round_trip y)))

instance optionalStoppingBHistCarrier : BHistCarrier OptionalStoppingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := optionalStoppingToEventFlow
  fromEventFlow := optionalStoppingFromEventFlow

instance optionalStoppingChapterTasteGate : ChapterTasteGate OptionalStoppingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change optionalStoppingFromEventFlow (optionalStoppingToEventFlow x) = some x
    exact optionalStopping_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (optionalStoppingToEventFlow_injective heq)

theorem OptionalStoppingTasteGate_single_carrier_alignment :
    optionalStoppingFromEventFlow
        (optionalStoppingToEventFlow
          (OptionalStoppingUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
      some
        (OptionalStoppingUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ∧
      optionalStoppingToEventFlow
        (OptionalStoppingUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        optionalStoppingToEventFlow
          (OptionalStoppingUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · rfl

end BEDC.Derived.OptionalStoppingUp
