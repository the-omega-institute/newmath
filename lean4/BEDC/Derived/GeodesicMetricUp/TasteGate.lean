import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeodesicMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GeodesicMetricUp : Type where
  | mk (M E T S A C R P N : BHist) : GeodesicMetricUp
  deriving DecidableEq

def geodesicMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: geodesicMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: geodesicMetricEncodeBHist h

def geodesicMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (geodesicMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (geodesicMetricDecodeBHist tail)

private theorem GeodesicMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, geodesicMetricDecodeBHist (geodesicMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def geodesicMetricFields : GeodesicMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GeodesicMetricUp.mk M E T S A C R P N => [M, E, T, S, A, C, R, P, N]

def geodesicMetricToEventFlow : GeodesicMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (geodesicMetricFields x).map geodesicMetricEncodeBHist

private def geodesicMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => geodesicMetricEventAtDefault index rest

def geodesicMetricFromEventFlow (ef : EventFlow) : Option GeodesicMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GeodesicMetricUp.mk
      (geodesicMetricDecodeBHist (geodesicMetricEventAtDefault 0 ef))
      (geodesicMetricDecodeBHist (geodesicMetricEventAtDefault 1 ef))
      (geodesicMetricDecodeBHist (geodesicMetricEventAtDefault 2 ef))
      (geodesicMetricDecodeBHist (geodesicMetricEventAtDefault 3 ef))
      (geodesicMetricDecodeBHist (geodesicMetricEventAtDefault 4 ef))
      (geodesicMetricDecodeBHist (geodesicMetricEventAtDefault 5 ef))
      (geodesicMetricDecodeBHist (geodesicMetricEventAtDefault 6 ef))
      (geodesicMetricDecodeBHist (geodesicMetricEventAtDefault 7 ef))
      (geodesicMetricDecodeBHist (geodesicMetricEventAtDefault 8 ef)))

private theorem GeodesicMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : GeodesicMetricUp,
      geodesicMetricFromEventFlow (geodesicMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E T S A C R P N =>
      change
        some
          (GeodesicMetricUp.mk
            (geodesicMetricDecodeBHist (geodesicMetricEncodeBHist M))
            (geodesicMetricDecodeBHist (geodesicMetricEncodeBHist E))
            (geodesicMetricDecodeBHist (geodesicMetricEncodeBHist T))
            (geodesicMetricDecodeBHist (geodesicMetricEncodeBHist S))
            (geodesicMetricDecodeBHist (geodesicMetricEncodeBHist A))
            (geodesicMetricDecodeBHist (geodesicMetricEncodeBHist C))
            (geodesicMetricDecodeBHist (geodesicMetricEncodeBHist R))
            (geodesicMetricDecodeBHist (geodesicMetricEncodeBHist P))
            (geodesicMetricDecodeBHist (geodesicMetricEncodeBHist N))) =
          some (GeodesicMetricUp.mk M E T S A C R P N)
      rw [GeodesicMetricTasteGate_single_carrier_alignment_decode M,
        GeodesicMetricTasteGate_single_carrier_alignment_decode E,
        GeodesicMetricTasteGate_single_carrier_alignment_decode T,
        GeodesicMetricTasteGate_single_carrier_alignment_decode S,
        GeodesicMetricTasteGate_single_carrier_alignment_decode A,
        GeodesicMetricTasteGate_single_carrier_alignment_decode C,
        GeodesicMetricTasteGate_single_carrier_alignment_decode R,
        GeodesicMetricTasteGate_single_carrier_alignment_decode P,
        GeodesicMetricTasteGate_single_carrier_alignment_decode N]

private theorem GeodesicMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GeodesicMetricUp} :
    geodesicMetricToEventFlow x = geodesicMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      geodesicMetricFromEventFlow (geodesicMetricToEventFlow x) =
        geodesicMetricFromEventFlow (geodesicMetricToEventFlow y) :=
    congrArg geodesicMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (GeodesicMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GeodesicMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem GeodesicMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : GeodesicMetricUp, geodesicMetricFields x = geodesicMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 E1 T1 S1 A1 C1 R1 P1 N1 =>
      cases y with
      | mk M2 E2 T2 S2 A2 C2 R2 P2 N2 =>
          cases hfields
          rfl

instance geodesicMetricBHistCarrier : BHistCarrier GeodesicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := geodesicMetricToEventFlow
  fromEventFlow := geodesicMetricFromEventFlow

instance geodesicMetricChapterTasteGate : ChapterTasteGate GeodesicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change geodesicMetricFromEventFlow (geodesicMetricToEventFlow x) = some x
    exact GeodesicMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GeodesicMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance geodesicMetricFieldFaithful : FieldFaithful GeodesicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := geodesicMetricFields
  field_faithful := GeodesicMetricTasteGate_single_carrier_alignment_fields

instance geodesicMetricNontrivial : Nontrivial GeodesicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GeodesicMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GeodesicMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GeodesicMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  geodesicMetricChapterTasteGate

theorem GeodesicMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, geodesicMetricDecodeBHist (geodesicMetricEncodeBHist h) = h) ∧
      (∀ x : GeodesicMetricUp,
        geodesicMetricFromEventFlow (geodesicMetricToEventFlow x) = some x) ∧
        (∀ x y : GeodesicMetricUp,
          geodesicMetricToEventFlow x = geodesicMetricToEventFlow y → x = y) ∧
          geodesicMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨GeodesicMetricTasteGate_single_carrier_alignment_decode,
      GeodesicMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => GeodesicMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.GeodesicMetricUp
