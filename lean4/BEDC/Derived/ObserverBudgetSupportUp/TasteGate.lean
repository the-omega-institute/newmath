import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverBudgetSupportUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverBudgetSupportUp : Type where
  | mk : (F S X B T H C P N : BHist) → ObserverBudgetSupportUp
  deriving DecidableEq

def observerBudgetSupportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerBudgetSupportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerBudgetSupportEncodeBHist h

def observerBudgetSupportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerBudgetSupportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerBudgetSupportDecodeBHist tail)

private theorem observerBudgetSupportDecode_encode_bhist :
    ∀ h : BHist,
      observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observerBudgetSupportFields : ObserverBudgetSupportUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverBudgetSupportUp.mk F S X B T H C P N => [F, S, X, B, T, H, C, P, N]

def observerBudgetSupportToEventFlow : ObserverBudgetSupportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverBudgetSupportUp.mk F S X B T H C P N =>
      [[BMark.b0],
        observerBudgetSupportEncodeBHist F,
        [BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerBudgetSupportEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist N]

private def observerBudgetSupportEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => observerBudgetSupportEventAtDefault index rest

def observerBudgetSupportFromEventFlow (ef : EventFlow) : Option ObserverBudgetSupportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ObserverBudgetSupportUp.mk
      (observerBudgetSupportDecodeBHist (observerBudgetSupportEventAtDefault 1 ef))
      (observerBudgetSupportDecodeBHist (observerBudgetSupportEventAtDefault 3 ef))
      (observerBudgetSupportDecodeBHist (observerBudgetSupportEventAtDefault 5 ef))
      (observerBudgetSupportDecodeBHist (observerBudgetSupportEventAtDefault 7 ef))
      (observerBudgetSupportDecodeBHist (observerBudgetSupportEventAtDefault 9 ef))
      (observerBudgetSupportDecodeBHist (observerBudgetSupportEventAtDefault 11 ef))
      (observerBudgetSupportDecodeBHist (observerBudgetSupportEventAtDefault 13 ef))
      (observerBudgetSupportDecodeBHist (observerBudgetSupportEventAtDefault 15 ef))
      (observerBudgetSupportDecodeBHist (observerBudgetSupportEventAtDefault 17 ef)))

private theorem observerBudgetSupport_round_trip :
    ∀ x : ObserverBudgetSupportUp,
      observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S X B T H C P N =>
      change
        some
          (ObserverBudgetSupportUp.mk
            (observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist F))
            (observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist S))
            (observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist X))
            (observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist B))
            (observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist T))
            (observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist H))
            (observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist C))
            (observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist P))
            (observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist N))) =
          some (ObserverBudgetSupportUp.mk F S X B T H C P N)
      rw [observerBudgetSupportDecode_encode_bhist F,
        observerBudgetSupportDecode_encode_bhist S,
        observerBudgetSupportDecode_encode_bhist X,
        observerBudgetSupportDecode_encode_bhist B,
        observerBudgetSupportDecode_encode_bhist T,
        observerBudgetSupportDecode_encode_bhist H,
        observerBudgetSupportDecode_encode_bhist C,
        observerBudgetSupportDecode_encode_bhist P,
        observerBudgetSupportDecode_encode_bhist N]

private theorem observerBudgetSupportToEventFlow_injective {x y : ObserverBudgetSupportUp} :
    observerBudgetSupportToEventFlow x = observerBudgetSupportToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow x) =
        observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow y) :=
    congrArg observerBudgetSupportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerBudgetSupport_round_trip x).symm
      (Eq.trans hread (observerBudgetSupport_round_trip y)))

private theorem observerBudgetSupport_fields_faithful :
    ∀ x y : ObserverBudgetSupportUp,
      observerBudgetSupportFields x = observerBudgetSupportFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ S₁ X₁ B₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ S₂ X₂ B₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance observerBudgetSupportBHistCarrier :
    BHistCarrier ObserverBudgetSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerBudgetSupportToEventFlow
  fromEventFlow := observerBudgetSupportFromEventFlow

instance observerBudgetSupportChapterTasteGate :
    ChapterTasteGate ObserverBudgetSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow x) = some x
    exact observerBudgetSupport_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerBudgetSupportToEventFlow_injective heq)

instance observerBudgetSupportFieldFaithful :
    FieldFaithful ObserverBudgetSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerBudgetSupportFields
  field_faithful := observerBudgetSupport_fields_faithful

instance observerBudgetSupportNontrivial :
    Nontrivial ObserverBudgetSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverBudgetSupportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverBudgetSupportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverBudgetSupportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerBudgetSupportChapterTasteGate

theorem ObserverBudgetSupportTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist h) = h) ∧
      (∀ x : ObserverBudgetSupportUp,
        observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow x) = some x) ∧
        (∀ x y : ObserverBudgetSupportUp,
          observerBudgetSupportToEventFlow x = observerBudgetSupportToEventFlow y →
            x = y) ∧
          observerBudgetSupportEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : ObserverBudgetSupportUp,
              observerBudgetSupportFields x = observerBudgetSupportFields y → x = y) ∧
              (∃ x y : ObserverBudgetSupportUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerBudgetSupportDecode_encode_bhist
  · constructor
    · exact observerBudgetSupport_round_trip
    · constructor
      · intro x y heq
        exact observerBudgetSupportToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact observerBudgetSupport_fields_faithful
          · exact
              ⟨(observerBudgetSupportNontrivial.witness_pair).fst,
                (observerBudgetSupportNontrivial.witness_pair).snd.fst,
                (observerBudgetSupportNontrivial.witness_pair).snd.snd⟩

end BEDC.Derived.ObserverBudgetSupportUp.TasteGate

namespace BEDC.Derived.ObserverBudgetSupportUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.ObserverBudgetSupportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.ObserverBudgetSupportUp
