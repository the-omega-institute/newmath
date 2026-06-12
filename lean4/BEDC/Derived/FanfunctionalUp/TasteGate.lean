import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FanfunctionalUp : Type where
  | mk (C F Eps B D W M H K P N : BHist) : FanfunctionalUp
  deriving DecidableEq

def fanFunctionalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fanFunctionalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fanFunctionalEncodeBHist h

def fanFunctionalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fanFunctionalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fanFunctionalDecodeBHist tail)

private theorem fanFunctionalDecode_encode :
    ∀ h : BHist, fanFunctionalDecodeBHist (fanFunctionalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fanFunctionalFields : FanfunctionalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FanfunctionalUp.mk C F Eps B D W M H K P N => [C, F, Eps, B, D, W, M, H, K, P, N]

def fanFunctionalToEventFlow : FanfunctionalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (fanFunctionalFields token).map fanFunctionalEncodeBHist

private def fanFunctionalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fanFunctionalEventAt index rest

def fanFunctionalFromEventFlow (flow : EventFlow) : Option FanfunctionalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FanfunctionalUp.mk
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 0 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 1 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 2 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 3 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 4 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 5 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 6 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 7 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 8 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 9 flow))
      (fanFunctionalDecodeBHist (fanFunctionalEventAt 10 flow)))

private theorem fanFunctional_round_trip :
    ∀ x : FanfunctionalUp, fanFunctionalFromEventFlow (fanFunctionalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C F Eps B D W M H K P N =>
      change
        some
            (FanfunctionalUp.mk
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist C))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist F))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist Eps))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist B))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist D))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist W))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist M))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist H))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist K))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist P))
              (fanFunctionalDecodeBHist (fanFunctionalEncodeBHist N))) =
          some (FanfunctionalUp.mk C F Eps B D W M H K P N)
      rw [fanFunctionalDecode_encode C, fanFunctionalDecode_encode F,
        fanFunctionalDecode_encode Eps, fanFunctionalDecode_encode B,
        fanFunctionalDecode_encode D, fanFunctionalDecode_encode W,
        fanFunctionalDecode_encode M, fanFunctionalDecode_encode H,
        fanFunctionalDecode_encode K, fanFunctionalDecode_encode P,
        fanFunctionalDecode_encode N]

private theorem fanFunctionalToEventFlow_injective {x y : FanfunctionalUp} :
    fanFunctionalToEventFlow x = fanFunctionalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fanFunctionalFromEventFlow (fanFunctionalToEventFlow x) =
        fanFunctionalFromEventFlow (fanFunctionalToEventFlow y) :=
    congrArg fanFunctionalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fanFunctional_round_trip x).symm
      (Eq.trans hread (fanFunctional_round_trip y)))

instance fanFunctionalBHistCarrier : BHistCarrier FanfunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fanFunctionalToEventFlow
  fromEventFlow := fanFunctionalFromEventFlow

instance fanFunctionalChapterTasteGate : ChapterTasteGate FanfunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fanFunctionalFromEventFlow (fanFunctionalToEventFlow x) = some x
    exact fanFunctional_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fanFunctionalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FanfunctionalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fanFunctionalChapterTasteGate

theorem FanFunctionalTasteGate_single_carrier_alignment :
    (fanFunctionalDecodeBHist [] = BHist.Empty) ∧
      (∀ h : BHist, fanFunctionalDecodeBHist (fanFunctionalEncodeBHist h) = h) ∧
        (∀ x : FanfunctionalUp, fanFunctionalFromEventFlow (fanFunctionalToEventFlow x) = some x) ∧
          Nonempty (BHistCarrier FanfunctionalUp) ∧
            Nonempty (ChapterTasteGate FanfunctionalUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, fanFunctionalDecode_encode, fanFunctional_round_trip,
      ⟨fanFunctionalBHistCarrier⟩, ⟨fanFunctionalChapterTasteGate⟩⟩

end BEDC.Derived.FanfunctionalUp
