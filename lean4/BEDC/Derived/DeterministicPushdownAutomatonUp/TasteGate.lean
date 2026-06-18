import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DeterministicPushdownAutomatonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DeterministicPushdownAutomatonUp : Type where
  | mk (Q Sigma Gamma delta q0 Z0 F w rho sigma e chi H C P N : BHist) :
      DeterministicPushdownAutomatonUp
  deriving DecidableEq

def deterministicPushdownAutomatonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: deterministicPushdownAutomatonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: deterministicPushdownAutomatonEncodeBHist h

def deterministicPushdownAutomatonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (deterministicPushdownAutomatonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (deterministicPushdownAutomatonDecodeBHist tail)

private theorem deterministicPushdownAutomaton_decode_encode :
    ∀ h : BHist,
      deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def deterministicPushdownAutomatonFields :
    DeterministicPushdownAutomatonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DeterministicPushdownAutomatonUp.mk Q Sigma Gamma delta q0 Z0 F w rho sigma e chi H C P N =>
      [Q, Sigma, Gamma, delta, q0, Z0, F, w, rho, sigma, e, chi, H, C, P, N]

def deterministicPushdownAutomatonToEventFlow :
    DeterministicPushdownAutomatonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (deterministicPushdownAutomatonFields x).map deterministicPushdownAutomatonEncodeBHist

private def deterministicPushdownAutomatonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => deterministicPushdownAutomatonEventAtDefault index rest

def deterministicPushdownAutomatonFromEventFlow
    (ef : EventFlow) : Option DeterministicPushdownAutomatonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DeterministicPushdownAutomatonUp.mk
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 0 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 1 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 2 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 3 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 4 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 5 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 6 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 7 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 8 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 9 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 10 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 11 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 12 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 13 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 14 ef))
      (deterministicPushdownAutomatonDecodeBHist
        (deterministicPushdownAutomatonEventAtDefault 15 ef)))

private theorem deterministicPushdownAutomaton_round_trip :
    ∀ x : DeterministicPushdownAutomatonUp,
      deterministicPushdownAutomatonFromEventFlow
        (deterministicPushdownAutomatonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q Sigma Gamma delta q0 Z0 F w rho sigma e chi H C P N =>
      change
        some
          (DeterministicPushdownAutomatonUp.mk
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist Q))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist Sigma))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist Gamma))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist delta))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist q0))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist Z0))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist F))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist w))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist rho))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist sigma))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist e))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist chi))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist H))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist C))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist P))
            (deterministicPushdownAutomatonDecodeBHist
              (deterministicPushdownAutomatonEncodeBHist N))) =
          some
            (DeterministicPushdownAutomatonUp.mk Q Sigma Gamma delta q0 Z0 F w rho
              sigma e chi H C P N)
      rw [deterministicPushdownAutomaton_decode_encode Q,
        deterministicPushdownAutomaton_decode_encode Sigma,
        deterministicPushdownAutomaton_decode_encode Gamma,
        deterministicPushdownAutomaton_decode_encode delta,
        deterministicPushdownAutomaton_decode_encode q0,
        deterministicPushdownAutomaton_decode_encode Z0,
        deterministicPushdownAutomaton_decode_encode F,
        deterministicPushdownAutomaton_decode_encode w,
        deterministicPushdownAutomaton_decode_encode rho,
        deterministicPushdownAutomaton_decode_encode sigma,
        deterministicPushdownAutomaton_decode_encode e,
        deterministicPushdownAutomaton_decode_encode chi,
        deterministicPushdownAutomaton_decode_encode H,
        deterministicPushdownAutomaton_decode_encode C,
        deterministicPushdownAutomaton_decode_encode P,
        deterministicPushdownAutomaton_decode_encode N]

private theorem deterministicPushdownAutomatonToEventFlow_injective
    {x y : DeterministicPushdownAutomatonUp} :
    deterministicPushdownAutomatonToEventFlow x =
      deterministicPushdownAutomatonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      deterministicPushdownAutomatonFromEventFlow
          (deterministicPushdownAutomatonToEventFlow x) =
        deterministicPushdownAutomatonFromEventFlow
          (deterministicPushdownAutomatonToEventFlow y) :=
    congrArg deterministicPushdownAutomatonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (deterministicPushdownAutomaton_round_trip x).symm
      (Eq.trans hread (deterministicPushdownAutomaton_round_trip y)))

instance deterministicPushdownAutomatonBHistCarrier :
    BHistCarrier DeterministicPushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := deterministicPushdownAutomatonToEventFlow
  fromEventFlow := deterministicPushdownAutomatonFromEventFlow

instance deterministicPushdownAutomatonChapterTasteGate :
    ChapterTasteGate DeterministicPushdownAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      deterministicPushdownAutomatonFromEventFlow
        (deterministicPushdownAutomatonToEventFlow x) = some x
    exact deterministicPushdownAutomaton_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (deterministicPushdownAutomatonToEventFlow_injective heq)

theorem DeterministicPushdownAutomatonTasteGate_single_carrier_alignment :
    deterministicPushdownAutomatonEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist,
        deterministicPushdownAutomatonDecodeBHist
          (deterministicPushdownAutomatonEncodeBHist h) = h) ∧
      (∀ x : DeterministicPushdownAutomatonUp,
        deterministicPushdownAutomatonFromEventFlow
          (deterministicPushdownAutomatonToEventFlow x) = some x) ∧
      Nonempty (BHistCarrier DeterministicPushdownAutomatonUp) ∧
        Nonempty (ChapterTasteGate DeterministicPushdownAutomatonUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl,
      deterministicPushdownAutomaton_decode_encode,
      deterministicPushdownAutomaton_round_trip,
      ⟨deterministicPushdownAutomatonBHistCarrier⟩,
      ⟨deterministicPushdownAutomatonChapterTasteGate⟩⟩

end BEDC.Derived.DeterministicPushdownAutomatonUp
