import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicRegularBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicRegularBridgeUp : Type where
  | mk (D W Q M E H C P N : BHist) : DyadicRegularBridgeUp
  deriving DecidableEq

def dyadicRegularBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicRegularBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicRegularBridgeEncodeBHist h

def dyadicRegularBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicRegularBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicRegularBridgeDecodeBHist tail)

private theorem dyadicRegularBridgeDecodeEncodeBHist :
    ∀ h : BHist, dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicRegularBridgeFields : DyadicRegularBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicRegularBridgeUp.mk D W Q M E H C P N => [D, W, Q, M, E, H, C, P, N]

def dyadicRegularBridgeToEventFlow : DyadicRegularBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicRegularBridgeFields x).map dyadicRegularBridgeEncodeBHist

private def dyadicRegularBridgeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicRegularBridgeEventAtDefault index rest

def dyadicRegularBridgeFromEventFlow (ef : EventFlow) : Option DyadicRegularBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicRegularBridgeUp.mk
      (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEventAtDefault 0 ef))
      (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEventAtDefault 1 ef))
      (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEventAtDefault 2 ef))
      (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEventAtDefault 3 ef))
      (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEventAtDefault 4 ef))
      (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEventAtDefault 5 ef))
      (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEventAtDefault 6 ef))
      (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEventAtDefault 7 ef))
      (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEventAtDefault 8 ef)))

private theorem dyadicRegularBridge_round_trip :
    ∀ x : DyadicRegularBridgeUp,
      dyadicRegularBridgeFromEventFlow (dyadicRegularBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W Q M E H C P N =>
      change
        some
          (DyadicRegularBridgeUp.mk
            (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist D))
            (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist W))
            (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist Q))
            (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist M))
            (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist E))
            (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist H))
            (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist C))
            (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist P))
            (dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist N))) =
          some (DyadicRegularBridgeUp.mk D W Q M E H C P N)
      rw [dyadicRegularBridgeDecodeEncodeBHist D, dyadicRegularBridgeDecodeEncodeBHist W,
        dyadicRegularBridgeDecodeEncodeBHist Q, dyadicRegularBridgeDecodeEncodeBHist M,
        dyadicRegularBridgeDecodeEncodeBHist E, dyadicRegularBridgeDecodeEncodeBHist H,
        dyadicRegularBridgeDecodeEncodeBHist C, dyadicRegularBridgeDecodeEncodeBHist P,
        dyadicRegularBridgeDecodeEncodeBHist N]

private theorem dyadicRegularBridgeToEventFlow_injective {x y : DyadicRegularBridgeUp} :
    dyadicRegularBridgeToEventFlow x = dyadicRegularBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicRegularBridgeFromEventFlow (dyadicRegularBridgeToEventFlow x) =
        dyadicRegularBridgeFromEventFlow (dyadicRegularBridgeToEventFlow y) :=
    congrArg dyadicRegularBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicRegularBridge_round_trip x).symm
      (Eq.trans hread (dyadicRegularBridge_round_trip y)))

private theorem dyadicRegularBridgeFields_faithful :
    ∀ x y : DyadicRegularBridgeUp, dyadicRegularBridgeFields x = dyadicRegularBridgeFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 W1 Q1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 W2 Q2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dyadicRegularBridgeBHistCarrier : BHistCarrier DyadicRegularBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicRegularBridgeToEventFlow
  fromEventFlow := dyadicRegularBridgeFromEventFlow

instance dyadicRegularBridgeChapterTasteGate : ChapterTasteGate DyadicRegularBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicRegularBridgeFromEventFlow (dyadicRegularBridgeToEventFlow x) = some x
    exact dyadicRegularBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicRegularBridgeToEventFlow_injective heq)

instance dyadicRegularBridgeFieldFaithful : FieldFaithful DyadicRegularBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicRegularBridgeFields
  field_faithful := dyadicRegularBridgeFields_faithful

def taste_gate : ChapterTasteGate DyadicRegularBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicRegularBridgeChapterTasteGate

theorem DyadicRegularBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicRegularBridgeDecodeBHist (dyadicRegularBridgeEncodeBHist h) = h) ∧
      (∀ x : DyadicRegularBridgeUp,
        dyadicRegularBridgeFromEventFlow (dyadicRegularBridgeToEventFlow x) = some x) ∧
        (∀ x y : DyadicRegularBridgeUp,
          dyadicRegularBridgeToEventFlow x = dyadicRegularBridgeToEventFlow y → x = y) ∧
          dyadicRegularBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨dyadicRegularBridgeDecodeEncodeBHist, dyadicRegularBridge_round_trip,
      fun _x _y heq => dyadicRegularBridgeToEventFlow_injective heq, rfl⟩

end BEDC.Derived.DyadicRegularBridgeUp
