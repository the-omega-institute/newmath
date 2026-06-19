import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PushdownAutomatonUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PushdownAutomatonUp : Type where
  | mk
      (Q Sigma Gamma delta q0 Z0 F w rho stack endpoint accept H C P N : BHist) :
      PushdownAutomatonUp
  deriving DecidableEq

def pushdownAutomatonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pushdownAutomatonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pushdownAutomatonEncodeBHist h

def pushdownAutomatonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pushdownAutomatonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pushdownAutomatonDecodeBHist tail)

private theorem pushdownAutomaton_decode_encode :
    ∀ h : BHist, pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def pushdownAutomatonFields : PushdownAutomatonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PushdownAutomatonUp.mk Q Sigma Gamma delta q0 Z0 F w rho stack endpoint accept H C P N =>
      [Q, Sigma, Gamma, delta, q0, Z0, F, w, rho, stack, endpoint, accept, H, C, P, N]

def pushdownAutomatonToEventFlow : PushdownAutomatonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (pushdownAutomatonFields x).map pushdownAutomatonEncodeBHist

private def pushdownAutomatonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pushdownAutomatonEventAtDefault index rest

def pushdownAutomatonFromEventFlow (ef : EventFlow) : Option PushdownAutomatonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PushdownAutomatonUp.mk
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 0 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 1 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 2 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 3 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 4 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 5 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 6 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 7 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 8 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 9 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 10 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 11 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 12 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 13 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 14 ef))
      (pushdownAutomatonDecodeBHist (pushdownAutomatonEventAtDefault 15 ef)))

private theorem pushdownAutomaton_round_trip :
    ∀ x : PushdownAutomatonUp,
      pushdownAutomatonFromEventFlow (pushdownAutomatonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q Sigma Gamma delta q0 Z0 F w rho stack endpoint accept H C P N =>
      change
        some
          (PushdownAutomatonUp.mk
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist Q))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist Sigma))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist Gamma))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist delta))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist q0))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist Z0))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist F))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist w))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist rho))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist stack))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist endpoint))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist accept))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist H))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist C))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist P))
            (pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist N))) =
          some
            (PushdownAutomatonUp.mk Q Sigma Gamma delta q0 Z0 F w rho stack endpoint
              accept H C P N)
      rw [pushdownAutomaton_decode_encode Q, pushdownAutomaton_decode_encode Sigma,
        pushdownAutomaton_decode_encode Gamma, pushdownAutomaton_decode_encode delta,
        pushdownAutomaton_decode_encode q0, pushdownAutomaton_decode_encode Z0,
        pushdownAutomaton_decode_encode F, pushdownAutomaton_decode_encode w,
        pushdownAutomaton_decode_encode rho, pushdownAutomaton_decode_encode stack,
        pushdownAutomaton_decode_encode endpoint, pushdownAutomaton_decode_encode accept,
        pushdownAutomaton_decode_encode H, pushdownAutomaton_decode_encode C,
        pushdownAutomaton_decode_encode P, pushdownAutomaton_decode_encode N]

private theorem pushdownAutomatonToEventFlow_injective {x y : PushdownAutomatonUp} :
    pushdownAutomatonToEventFlow x = pushdownAutomatonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pushdownAutomatonFromEventFlow (pushdownAutomatonToEventFlow x) =
        pushdownAutomatonFromEventFlow (pushdownAutomatonToEventFlow y) :=
    congrArg pushdownAutomatonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (pushdownAutomaton_round_trip x).symm
      (Eq.trans hread (pushdownAutomaton_round_trip y)))

private theorem pushdownAutomaton_field_faithful :
    ∀ x y : PushdownAutomatonUp, pushdownAutomatonFields x = pushdownAutomatonFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q Sigma Gamma delta q0 Z0 F w rho stack endpoint accept H C P N =>
      cases y with
      | mk Q' Sigma' Gamma' delta' q0' Z0' F' w' rho' stack' endpoint' accept' H' C' P' N' =>
          cases hfields
          rfl

instance pushdownAutomatonBHistCarrier : BHistCarrier PushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pushdownAutomatonToEventFlow
  fromEventFlow := pushdownAutomatonFromEventFlow

instance pushdownAutomatonChapterTasteGate : ChapterTasteGate PushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change pushdownAutomatonFromEventFlow (pushdownAutomatonToEventFlow x) = some x
    exact pushdownAutomaton_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pushdownAutomatonToEventFlow_injective heq)

instance pushdownAutomatonFieldFaithful : FieldFaithful PushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pushdownAutomatonFields
  field_faithful := pushdownAutomaton_field_faithful

instance pushdownAutomatonNontrivial : Nontrivial PushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PushdownAutomatonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PushdownAutomatonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PushdownAutomatonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pushdownAutomatonChapterTasteGate

theorem PushdownAutomatonTasteGate_single_carrier_alignment :
    (∀ h : BHist, pushdownAutomatonDecodeBHist (pushdownAutomatonEncodeBHist h) = h) ∧
      (∀ x : PushdownAutomatonUp,
        pushdownAutomatonFromEventFlow (pushdownAutomatonToEventFlow x) = some x) ∧
        (∀ x y : PushdownAutomatonUp,
          pushdownAutomatonToEventFlow x = pushdownAutomatonToEventFlow y → x = y) ∧
          pushdownAutomatonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨pushdownAutomaton_decode_encode, pushdownAutomaton_round_trip,
      (fun _ _ heq => pushdownAutomatonToEventFlow_injective heq), rfl⟩

end BEDC.Derived.PushdownAutomatonUp.TasteGate
