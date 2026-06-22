import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionSeparableCoreUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionSeparableCoreUp : Type where
  | mk (M D W E I J Q R L H C P N : BHist) : MetricCompletionSeparableCoreUp
  deriving DecidableEq

def metricCompletionSeparableCoreEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionSeparableCoreEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionSeparableCoreEncodeBHist h

def metricCompletionSeparableCoreDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionSeparableCoreDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionSeparableCoreDecodeBHist tail)

private theorem MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionSeparableCoreFields : MetricCompletionSeparableCoreUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionSeparableCoreUp.mk M D W E I J Q R L H C P N =>
      [M, D, W, E, I, J, Q, R, L, H, C, P, N]

def metricCompletionSeparableCoreToEventFlow :
    MetricCompletionSeparableCoreUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (metricCompletionSeparableCoreFields x).map
    metricCompletionSeparableCoreEncodeBHist

private def metricCompletionSeparableCoreEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionSeparableCoreEventAtDefault index rest

def metricCompletionSeparableCoreFromEventFlow
    (ef : EventFlow) : Option MetricCompletionSeparableCoreUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionSeparableCoreUp.mk
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 0 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 1 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 2 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 3 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 4 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 5 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 6 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 7 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 8 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 9 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 10 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 11 ef))
      (metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEventAtDefault 12 ef)))

private theorem MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricCompletionSeparableCoreUp,
      metricCompletionSeparableCoreFromEventFlow
        (metricCompletionSeparableCoreToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D W E I J Q R L H C P N =>
      change
        some
          (MetricCompletionSeparableCoreUp.mk
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist M))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist D))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist W))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist E))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist I))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist J))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist Q))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist R))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist L))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist H))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist C))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist P))
            (metricCompletionSeparableCoreDecodeBHist
              (metricCompletionSeparableCoreEncodeBHist N))) =
          some (MetricCompletionSeparableCoreUp.mk M D W E I J Q R L H C P N)
      rw [MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode M,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode D,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode W,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode E,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode I,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode J,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode Q,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode R,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode L,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode H,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode C,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode P,
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode N]

private theorem MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionSeparableCoreUp} :
    metricCompletionSeparableCoreToEventFlow x =
      metricCompletionSeparableCoreToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionSeparableCoreFromEventFlow
          (metricCompletionSeparableCoreToEventFlow x) =
        metricCompletionSeparableCoreFromEventFlow
          (metricCompletionSeparableCoreToEventFlow y) :=
    congrArg metricCompletionSeparableCoreFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_fields :
    ∀ x y : MetricCompletionSeparableCoreUp,
      metricCompletionSeparableCoreFields x = metricCompletionSeparableCoreFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 D1 W1 E1 I1 J1 Q1 R1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 D2 W2 E2 I2 J2 Q2 R2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metricCompletionSeparableCoreBHistCarrier :
    BHistCarrier MetricCompletionSeparableCoreUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionSeparableCoreToEventFlow
  fromEventFlow := metricCompletionSeparableCoreFromEventFlow

instance metricCompletionSeparableCoreChapterTasteGate :
    ChapterTasteGate MetricCompletionSeparableCoreUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionSeparableCoreFromEventFlow
        (metricCompletionSeparableCoreToEventFlow x) = some x
    exact MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metricCompletionSeparableCoreFieldFaithful :
    FieldFaithful MetricCompletionSeparableCoreUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCompletionSeparableCoreFields
  field_faithful := MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_fields

instance metricCompletionSeparableCoreNontrivial :
    Nontrivial MetricCompletionSeparableCoreUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricCompletionSeparableCoreUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      MetricCompletionSeparableCoreUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricCompletionSeparableCoreUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCompletionSeparableCoreChapterTasteGate

theorem MetricCompletionSeparableCoreTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metricCompletionSeparableCoreDecodeBHist
        (metricCompletionSeparableCoreEncodeBHist h) = h) ∧
      (∀ x : MetricCompletionSeparableCoreUp,
        metricCompletionSeparableCoreFromEventFlow
          (metricCompletionSeparableCoreToEventFlow x) = some x) ∧
        (∀ x y : MetricCompletionSeparableCoreUp,
          metricCompletionSeparableCoreToEventFlow x =
            metricCompletionSeparableCoreToEventFlow y → x = y) ∧
          metricCompletionSeparableCoreEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_decode,
      MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetricCompletionSeparableCoreTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricCompletionSeparableCoreUp
