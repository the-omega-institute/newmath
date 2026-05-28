import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeakDerivativeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeakDerivativeUp : Type where
  | mk (A D E Q W H C P N : BHist) : WeakDerivativeUp
  deriving DecidableEq

def weakDerivativeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weakDerivativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weakDerivativeEncodeBHist h

def weakDerivativeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weakDerivativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weakDerivativeDecodeBHist tail)

private theorem WeakDerivativeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, weakDerivativeDecodeBHist (weakDerivativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def weakDerivativeFields : WeakDerivativeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeakDerivativeUp.mk A D E Q W H C P N => [A, D, E, Q, W, H, C, P, N]

def weakDerivativeToEventFlow : WeakDerivativeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (weakDerivativeFields x).map weakDerivativeEncodeBHist

private def weakDerivativeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => weakDerivativeEventAtDefault index rest

def weakDerivativeFromEventFlow (ef : EventFlow) : Option WeakDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WeakDerivativeUp.mk
      (weakDerivativeDecodeBHist (weakDerivativeEventAtDefault 0 ef))
      (weakDerivativeDecodeBHist (weakDerivativeEventAtDefault 1 ef))
      (weakDerivativeDecodeBHist (weakDerivativeEventAtDefault 2 ef))
      (weakDerivativeDecodeBHist (weakDerivativeEventAtDefault 3 ef))
      (weakDerivativeDecodeBHist (weakDerivativeEventAtDefault 4 ef))
      (weakDerivativeDecodeBHist (weakDerivativeEventAtDefault 5 ef))
      (weakDerivativeDecodeBHist (weakDerivativeEventAtDefault 6 ef))
      (weakDerivativeDecodeBHist (weakDerivativeEventAtDefault 7 ef))
      (weakDerivativeDecodeBHist (weakDerivativeEventAtDefault 8 ef)))

private theorem WeakDerivativeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : WeakDerivativeUp,
      weakDerivativeFromEventFlow (weakDerivativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A D E Q W H C P N =>
      change
        some
          (WeakDerivativeUp.mk
            (weakDerivativeDecodeBHist (weakDerivativeEncodeBHist A))
            (weakDerivativeDecodeBHist (weakDerivativeEncodeBHist D))
            (weakDerivativeDecodeBHist (weakDerivativeEncodeBHist E))
            (weakDerivativeDecodeBHist (weakDerivativeEncodeBHist Q))
            (weakDerivativeDecodeBHist (weakDerivativeEncodeBHist W))
            (weakDerivativeDecodeBHist (weakDerivativeEncodeBHist H))
            (weakDerivativeDecodeBHist (weakDerivativeEncodeBHist C))
            (weakDerivativeDecodeBHist (weakDerivativeEncodeBHist P))
            (weakDerivativeDecodeBHist (weakDerivativeEncodeBHist N))) =
          some (WeakDerivativeUp.mk A D E Q W H C P N)
      rw [WeakDerivativeTasteGate_single_carrier_alignment_decode A,
        WeakDerivativeTasteGate_single_carrier_alignment_decode D,
        WeakDerivativeTasteGate_single_carrier_alignment_decode E,
        WeakDerivativeTasteGate_single_carrier_alignment_decode Q,
        WeakDerivativeTasteGate_single_carrier_alignment_decode W,
        WeakDerivativeTasteGate_single_carrier_alignment_decode H,
        WeakDerivativeTasteGate_single_carrier_alignment_decode C,
        WeakDerivativeTasteGate_single_carrier_alignment_decode P,
        WeakDerivativeTasteGate_single_carrier_alignment_decode N]

private theorem WeakDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WeakDerivativeUp} :
    weakDerivativeToEventFlow x = weakDerivativeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weakDerivativeFromEventFlow (weakDerivativeToEventFlow x) =
        weakDerivativeFromEventFlow (weakDerivativeToEventFlow y) :=
    congrArg weakDerivativeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WeakDerivativeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WeakDerivativeTasteGate_single_carrier_alignment_round_trip y)))

private theorem WeakDerivativeTasteGate_single_carrier_alignment_fields :
    ∀ x y : WeakDerivativeUp, weakDerivativeFields x = weakDerivativeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 D1 E1 Q1 W1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 D2 E2 Q2 W2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance weakDerivativeBHistCarrier : BHistCarrier WeakDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weakDerivativeToEventFlow
  fromEventFlow := weakDerivativeFromEventFlow

instance weakDerivativeChapterTasteGate : ChapterTasteGate WeakDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change weakDerivativeFromEventFlow (weakDerivativeToEventFlow x) = some x
    exact WeakDerivativeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WeakDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance weakDerivativeFieldFaithful : FieldFaithful WeakDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := weakDerivativeFields
  field_faithful := WeakDerivativeTasteGate_single_carrier_alignment_fields

instance weakDerivativeNontrivial : Nontrivial WeakDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WeakDerivativeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WeakDerivativeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WeakDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weakDerivativeChapterTasteGate

theorem WeakDerivativeTasteGate_single_carrier_alignment :
    (∀ h : BHist, weakDerivativeDecodeBHist (weakDerivativeEncodeBHist h) = h) ∧
      (∀ x : WeakDerivativeUp,
        weakDerivativeFromEventFlow (weakDerivativeToEventFlow x) = some x) ∧
        (∀ x y : WeakDerivativeUp,
          weakDerivativeToEventFlow x = weakDerivativeToEventFlow y → x = y) ∧
          weakDerivativeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨WeakDerivativeTasteGate_single_carrier_alignment_decode,
      WeakDerivativeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => WeakDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.WeakDerivativeUp
