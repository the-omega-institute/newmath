import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricClosedBallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricClosedBallUp : Type where
  | mk
      (metricSpace distanceWitness center radius radiusLedger membership transport route
        provenance nameCert : BHist) :
      MetricClosedBallUp
  deriving DecidableEq

def metricClosedBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricClosedBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricClosedBallEncodeBHist h

def metricClosedBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricClosedBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricClosedBallDecodeBHist tail)

private theorem metricClosedBall_decode_encode_bhist :
    ∀ h : BHist, metricClosedBallDecodeBHist (metricClosedBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricClosedBallFields : MetricClosedBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricClosedBallUp.mk metricSpace distanceWitness center radius radiusLedger membership
      transport route provenance nameCert =>
      [metricSpace, distanceWitness, center, radius, radiusLedger, membership, transport, route,
        provenance, nameCert]

def metricClosedBallToEventFlow : MetricClosedBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricClosedBallFields x).map metricClosedBallEncodeBHist

private def metricClosedBallEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricClosedBallEventAtDefault index rest

def metricClosedBallFromEventFlow : EventFlow → Option MetricClosedBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetricClosedBallUp.mk
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 0 ef))
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 1 ef))
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 2 ef))
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 3 ef))
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 4 ef))
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 5 ef))
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 6 ef))
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 7 ef))
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 8 ef))
        (metricClosedBallDecodeBHist (metricClosedBallEventAtDefault 9 ef)))

private theorem metricClosedBall_round_trip :
    ∀ x : MetricClosedBallUp,
      metricClosedBallFromEventFlow (metricClosedBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metricSpace distanceWitness center radius radiusLedger membership transport route
      provenance nameCert =>
      change
        some
          (MetricClosedBallUp.mk
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist metricSpace))
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist distanceWitness))
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist center))
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist radius))
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist radiusLedger))
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist membership))
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist transport))
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist route))
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist provenance))
            (metricClosedBallDecodeBHist (metricClosedBallEncodeBHist nameCert))) =
          some
            (MetricClosedBallUp.mk metricSpace distanceWitness center radius radiusLedger
              membership transport route provenance nameCert)
      rw [metricClosedBall_decode_encode_bhist metricSpace,
        metricClosedBall_decode_encode_bhist distanceWitness,
        metricClosedBall_decode_encode_bhist center,
        metricClosedBall_decode_encode_bhist radius,
        metricClosedBall_decode_encode_bhist radiusLedger,
        metricClosedBall_decode_encode_bhist membership,
        metricClosedBall_decode_encode_bhist transport,
        metricClosedBall_decode_encode_bhist route,
        metricClosedBall_decode_encode_bhist provenance,
        metricClosedBall_decode_encode_bhist nameCert]

private theorem metricClosedBallToEventFlow_injective {x y : MetricClosedBallUp} :
    metricClosedBallToEventFlow x = metricClosedBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricClosedBallFromEventFlow (metricClosedBallToEventFlow x) =
        metricClosedBallFromEventFlow (metricClosedBallToEventFlow y) :=
    congrArg metricClosedBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricClosedBall_round_trip x).symm
      (Eq.trans hread (metricClosedBall_round_trip y)))

private theorem metricClosedBall_field_faithful :
    ∀ x y : MetricClosedBallUp, metricClosedBallFields x = metricClosedBallFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metricSpace₁ distanceWitness₁ center₁ radius₁ radiusLedger₁ membership₁ transport₁
      route₁ provenance₁ nameCert₁ =>
      cases y with
      | mk metricSpace₂ distanceWitness₂ center₂ radius₂ radiusLedger₂ membership₂ transport₂
          route₂ provenance₂ nameCert₂ =>
          injection hfields with hMetricSpace tail0
          injection tail0 with hDistanceWitness tail1
          injection tail1 with hCenter tail2
          injection tail2 with hRadius tail3
          injection tail3 with hRadiusLedger tail4
          injection tail4 with hMembership tail5
          injection tail5 with hTransport tail6
          injection tail6 with hRoute tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hNameCert _
          subst hMetricSpace
          subst hDistanceWitness
          subst hCenter
          subst hRadius
          subst hRadiusLedger
          subst hMembership
          subst hTransport
          subst hRoute
          subst hProvenance
          subst hNameCert
          rfl

instance metricClosedBallBHistCarrier : BHistCarrier MetricClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricClosedBallToEventFlow
  fromEventFlow := metricClosedBallFromEventFlow

instance metricClosedBallChapterTasteGate : ChapterTasteGate MetricClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricClosedBallFromEventFlow (metricClosedBallToEventFlow x) = some x
    exact metricClosedBall_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricClosedBallToEventFlow_injective heq)

instance metricClosedBallFieldFaithful : FieldFaithful MetricClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricClosedBallFields
  field_faithful := metricClosedBall_field_faithful

instance metricClosedBallNontrivial : BEDC.Meta.TasteGate.Nontrivial MetricClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricClosedBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricClosedBallUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricClosedBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricClosedBallChapterTasteGate

theorem MetricClosedBallTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetricClosedBallUp) ∧
      Nonempty (FieldFaithful MetricClosedBallUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MetricClosedBallUp) ∧
          (∀ h : BHist, metricClosedBallDecodeBHist (metricClosedBallEncodeBHist h) = h) ∧
            (∀ x : MetricClosedBallUp,
              metricClosedBallFromEventFlow (metricClosedBallToEventFlow x) = some x) ∧
              (∀ x y : MetricClosedBallUp,
                metricClosedBallToEventFlow x = metricClosedBallToEventFlow y -> x = y) ∧
                metricClosedBallEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨metricClosedBallChapterTasteGate⟩,
      ⟨metricClosedBallFieldFaithful⟩,
      ⟨metricClosedBallNontrivial⟩,
      metricClosedBall_decode_encode_bhist,
      metricClosedBall_round_trip,
      (fun _ _ heq => metricClosedBallToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricClosedBallUp
