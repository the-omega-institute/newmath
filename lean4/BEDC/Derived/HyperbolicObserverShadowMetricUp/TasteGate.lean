import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicObserverShadowMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicObserverShadowMetricUp : Type where
  | mk (S M W R E F H C P N : BHist) : HyperbolicObserverShadowMetricUp
  deriving DecidableEq

def hyperbolicObserverShadowMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicObserverShadowMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicObserverShadowMetricEncodeBHist h

def hyperbolicObserverShadowMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicObserverShadowMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicObserverShadowMetricDecodeBHist tail)

private theorem HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hyperbolicObserverShadowMetricDecodeBHist
          (hyperbolicObserverShadowMetricEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicObserverShadowMetricFields :
    HyperbolicObserverShadowMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicObserverShadowMetricUp.mk S M W R E F H C P N =>
      [S, M, W, R, E, F, H, C, P, N]

def hyperbolicObserverShadowMetricToEventFlow :
    HyperbolicObserverShadowMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (hyperbolicObserverShadowMetricFields x).map
      hyperbolicObserverShadowMetricEncodeBHist

private def hyperbolicObserverShadowMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      hyperbolicObserverShadowMetricEventAtDefault index rest

def hyperbolicObserverShadowMetricFromEventFlow
    (flow : EventFlow) : Option HyperbolicObserverShadowMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicObserverShadowMetricUp.mk
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 0 flow))
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 1 flow))
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 2 flow))
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 3 flow))
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 4 flow))
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 5 flow))
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 6 flow))
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 7 flow))
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 8 flow))
      (hyperbolicObserverShadowMetricDecodeBHist
        (hyperbolicObserverShadowMetricEventAtDefault 9 flow)))

private theorem HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HyperbolicObserverShadowMetricUp,
      hyperbolicObserverShadowMetricFromEventFlow
          (hyperbolicObserverShadowMetricToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M W R E F H C P N =>
      change
        some
            (HyperbolicObserverShadowMetricUp.mk
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist S))
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist M))
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist W))
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist R))
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist E))
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist F))
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist H))
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist C))
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist P))
              (hyperbolicObserverShadowMetricDecodeBHist
                (hyperbolicObserverShadowMetricEncodeBHist N))) =
          some (HyperbolicObserverShadowMetricUp.mk S M W R E F H C P N)
      rw [HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode S,
        HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode M,
        HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode W,
        HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode R,
        HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode E,
        HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode F,
        HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode H,
        HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode C,
        HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode P,
        HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode N]

private theorem HyperbolicObserverShadowMetricToEventFlow_injective
    {x y : HyperbolicObserverShadowMetricUp} :
    hyperbolicObserverShadowMetricToEventFlow x =
        hyperbolicObserverShadowMetricToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      hyperbolicObserverShadowMetricFromEventFlow
          (hyperbolicObserverShadowMetricToEventFlow x) =
        hyperbolicObserverShadowMetricFromEventFlow
          (hyperbolicObserverShadowMetricToEventFlow y) :=
    congrArg hyperbolicObserverShadowMetricFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans
      (HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicObserverShadowMetric_field_faithful :
    ∀ x y : HyperbolicObserverShadowMetricUp,
      hyperbolicObserverShadowMetricFields x =
          hyperbolicObserverShadowMetricFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 M1 W1 R1 E1 F1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 M2 W2 R2 E2 F2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyperbolicObserverShadowMetricBHistCarrier :
    BHistCarrier HyperbolicObserverShadowMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicObserverShadowMetricToEventFlow
  fromEventFlow := hyperbolicObserverShadowMetricFromEventFlow

instance hyperbolicObserverShadowMetricChapterTasteGate :
    ChapterTasteGate HyperbolicObserverShadowMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicObserverShadowMetricFromEventFlow
          (hyperbolicObserverShadowMetricToEventFlow x) =
        some x
    exact HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicObserverShadowMetricToEventFlow_injective heq)

instance hyperbolicObserverShadowMetricFieldFaithful :
    FieldFaithful HyperbolicObserverShadowMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicObserverShadowMetricFields
  field_faithful := HyperbolicObserverShadowMetric_field_faithful

instance hyperbolicObserverShadowMetricNontrivial :
    Nontrivial HyperbolicObserverShadowMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicObserverShadowMetricUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      HyperbolicObserverShadowMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HyperbolicObserverShadowMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicObserverShadowMetricChapterTasteGate

theorem HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicObserverShadowMetricDecodeBHist
          (hyperbolicObserverShadowMetricEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier HyperbolicObserverShadowMetricUp) ∧
        Nonempty (ChapterTasteGate HyperbolicObserverShadowMetricUp) ∧
          Nonempty (FieldFaithful HyperbolicObserverShadowMetricUp) ∧
            Nonempty (BEDC.Meta.TasteGate.Nontrivial HyperbolicObserverShadowMetricUp) ∧
              hyperbolicObserverShadowMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨HyperbolicObserverShadowMetricTasteGate_single_carrier_alignment_decode,
      ⟨hyperbolicObserverShadowMetricBHistCarrier⟩,
      ⟨hyperbolicObserverShadowMetricChapterTasteGate⟩,
      ⟨hyperbolicObserverShadowMetricFieldFaithful⟩,
      ⟨hyperbolicObserverShadowMetricNontrivial⟩,
      rfl⟩

end BEDC.Derived.HyperbolicObserverShadowMetricUp
