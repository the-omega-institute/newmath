import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCauchyNetClusterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCauchyNetClusterUp : Type where
  | mk (D W M J S R T E H C P N : BHist) : MetricCauchyNetClusterUp
  deriving DecidableEq

def metricCauchyNetClusterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCauchyNetClusterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCauchyNetClusterEncodeBHist h

def metricCauchyNetClusterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCauchyNetClusterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCauchyNetClusterDecodeBHist tail)

private theorem MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCauchyNetClusterFields : MetricCauchyNetClusterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCauchyNetClusterUp.mk D W M J S R T E H C P N =>
      [D, W, M, J, S, R, T, E, H, C, P, N]

def metricCauchyNetClusterToEventFlow : MetricCauchyNetClusterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCauchyNetClusterFields x).map metricCauchyNetClusterEncodeBHist

private def metricCauchyNetClusterEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCauchyNetClusterEventAt index rest

def metricCauchyNetClusterFromEventFlow
    (ef : EventFlow) : Option MetricCauchyNetClusterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCauchyNetClusterUp.mk
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 0 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 1 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 2 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 3 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 4 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 5 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 6 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 7 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 8 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 9 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 10 ef))
      (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEventAt 11 ef)))

private theorem MetricCauchyNetClusterTasteGate_single_carrier_alignment_round_trip
    (x : MetricCauchyNetClusterUp) :
    metricCauchyNetClusterFromEventFlow
      (metricCauchyNetClusterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D W M J S R T E H C P N =>
      change
        some
          (MetricCauchyNetClusterUp.mk
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist D))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist W))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist M))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist J))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist S))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist R))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist T))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist E))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist H))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist C))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist P))
            (metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist N))) =
          some (MetricCauchyNetClusterUp.mk D W M J S R T E H C P N)
      rw [MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode D,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode W,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode M,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode J,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode S,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode R,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode T,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode E,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode H,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode C,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode P,
        MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode N]

private theorem MetricCauchyNetClusterTasteGate_single_carrier_alignment_injective
    {x y : MetricCauchyNetClusterUp} :
    metricCauchyNetClusterToEventFlow x =
      metricCauchyNetClusterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCauchyNetClusterFromEventFlow (metricCauchyNetClusterToEventFlow x) =
        metricCauchyNetClusterFromEventFlow (metricCauchyNetClusterToEventFlow y) :=
    congrArg metricCauchyNetClusterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCauchyNetClusterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCauchyNetClusterTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricCauchyNetClusterTasteGate_single_carrier_alignment_fields
    (x y : MetricCauchyNetClusterUp) :
    metricCauchyNetClusterFields x = metricCauchyNetClusterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  intro hfields
  cases x with
  | mk D1 W1 M1 J1 S1 R1 T1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 W2 M2 J2 S2 R2 T2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metricCauchyNetClusterBHistCarrier :
    BHistCarrier MetricCauchyNetClusterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCauchyNetClusterToEventFlow
  fromEventFlow := metricCauchyNetClusterFromEventFlow

instance metricCauchyNetClusterChapterTasteGate :
    ChapterTasteGate MetricCauchyNetClusterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCauchyNetClusterFromEventFlow
        (metricCauchyNetClusterToEventFlow x) = some x
    exact MetricCauchyNetClusterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricCauchyNetClusterTasteGate_single_carrier_alignment_injective heq)

instance metricCauchyNetClusterFieldFaithful :
    FieldFaithful MetricCauchyNetClusterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCauchyNetClusterFields
  field_faithful := MetricCauchyNetClusterTasteGate_single_carrier_alignment_fields

instance metricCauchyNetClusterNontrivial :
    Nontrivial MetricCauchyNetClusterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricCauchyNetClusterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      MetricCauchyNetClusterUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricCauchyNetClusterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCauchyNetClusterChapterTasteGate

theorem MetricCauchyNetClusterTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metricCauchyNetClusterDecodeBHist (metricCauchyNetClusterEncodeBHist h) = h) /\
      (forall x : MetricCauchyNetClusterUp,
        metricCauchyNetClusterFromEventFlow
          (metricCauchyNetClusterToEventFlow x) = some x) /\
        (forall x y : MetricCauchyNetClusterUp,
          metricCauchyNetClusterToEventFlow x =
            metricCauchyNetClusterToEventFlow y -> x = y) /\
          metricCauchyNetClusterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MetricCauchyNetClusterTasteGate_single_carrier_alignment_decode,
      MetricCauchyNetClusterTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => MetricCauchyNetClusterTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.MetricCauchyNetClusterUp
