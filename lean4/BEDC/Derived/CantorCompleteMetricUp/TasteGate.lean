import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorCompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorCompleteMetricUp : Type where
  | mk
      (M B F D W Q E H C P N : BHist) :
      CantorCompleteMetricUp
  deriving DecidableEq

def cantorCompleteMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorCompleteMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorCompleteMetricEncodeBHist h

def cantorCompleteMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorCompleteMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorCompleteMetricDecodeBHist tail)

private theorem cantorCompleteMetric_decode_encode :
    ∀ h : BHist,
      cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorCompleteMetricFields : CantorCompleteMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorCompleteMetricUp.mk M B F D W Q E H C P N =>
      [M, B, F, D, W, Q, E, H, C, P, N]

def cantorCompleteMetricToEventFlow : CantorCompleteMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cantorCompleteMetricFields x).map cantorCompleteMetricEncodeBHist

private def cantorCompleteMetricEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorCompleteMetricEventAt index rest

def cantorCompleteMetricFromEventFlow : EventFlow → Option CantorCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CantorCompleteMetricUp.mk
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 0 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 1 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 2 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 3 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 4 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 5 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 6 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 7 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 8 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 9 ef))
        (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEventAt 10 ef)))

private theorem cantorCompleteMetric_round_trip :
    ∀ x : CantorCompleteMetricUp,
      cantorCompleteMetricFromEventFlow (cantorCompleteMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M B F D W Q E H C P N =>
      change
        some
          (CantorCompleteMetricUp.mk
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist M))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist B))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist F))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist D))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist W))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist Q))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist E))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist H))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist C))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist P))
            (cantorCompleteMetricDecodeBHist (cantorCompleteMetricEncodeBHist N))) =
          some (CantorCompleteMetricUp.mk M B F D W Q E H C P N)
      rw [cantorCompleteMetric_decode_encode M, cantorCompleteMetric_decode_encode B,
        cantorCompleteMetric_decode_encode F, cantorCompleteMetric_decode_encode D,
        cantorCompleteMetric_decode_encode W, cantorCompleteMetric_decode_encode Q,
        cantorCompleteMetric_decode_encode E, cantorCompleteMetric_decode_encode H,
        cantorCompleteMetric_decode_encode C, cantorCompleteMetric_decode_encode P,
        cantorCompleteMetric_decode_encode N]

private theorem cantorCompleteMetricToEventFlow_injective {x y : CantorCompleteMetricUp} :
    cantorCompleteMetricToEventFlow x = cantorCompleteMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorCompleteMetricFromEventFlow (cantorCompleteMetricToEventFlow x) =
        cantorCompleteMetricFromEventFlow (cantorCompleteMetricToEventFlow y) :=
    congrArg cantorCompleteMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cantorCompleteMetric_round_trip x).symm
      (Eq.trans hread (cantorCompleteMetric_round_trip y)))

private theorem cantorCompleteMetricFields_faithful :
    ∀ x y : CantorCompleteMetricUp,
      cantorCompleteMetricFields x = cantorCompleteMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ B₁ F₁ D₁ W₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ B₂ F₂ D₂ W₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cantorCompleteMetricBHistCarrier :
    BHistCarrier CantorCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorCompleteMetricToEventFlow
  fromEventFlow := cantorCompleteMetricFromEventFlow

instance cantorCompleteMetricChapterTasteGate :
    ChapterTasteGate CantorCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorCompleteMetricFromEventFlow (cantorCompleteMetricToEventFlow x) = some x
    exact cantorCompleteMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cantorCompleteMetricToEventFlow_injective heq)

instance cantorCompleteMetricFieldFaithful :
    FieldFaithful CantorCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cantorCompleteMetricFields
  field_faithful := cantorCompleteMetricFields_faithful

instance cantorCompleteMetricNontrivial :
    Nontrivial CantorCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CantorCompleteMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CantorCompleteMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def cantorCompleteMetricTasteGate : ChapterTasteGate CantorCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorCompleteMetricChapterTasteGate

theorem CantorCompleteMetricTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CantorCompleteMetricUp) ∧
      Nonempty (FieldFaithful CantorCompleteMetricUp) ∧
      Nonempty (Nontrivial CantorCompleteMetricUp) ∧
      (∀ h : BHist, cantorCompleteMetricDecodeBHist
        (cantorCompleteMetricEncodeBHist h) = h) ∧
      (∀ x : CantorCompleteMetricUp,
        cantorCompleteMetricFromEventFlow (cantorCompleteMetricToEventFlow x) = some x) ∧
      (∀ x y : CantorCompleteMetricUp,
        cantorCompleteMetricToEventFlow x = cantorCompleteMetricToEventFlow y → x = y) ∧
      cantorCompleteMetricEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨cantorCompleteMetricChapterTasteGate⟩,
      ⟨cantorCompleteMetricFieldFaithful⟩,
      ⟨cantorCompleteMetricNontrivial⟩,
      cantorCompleteMetric_decode_encode,
      cantorCompleteMetric_round_trip,
      (fun _ _ heq => cantorCompleteMetricToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CantorCompleteMetricUp
