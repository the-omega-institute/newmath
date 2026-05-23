import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedMetricUp : Type where
  | mk (X M D S R E Z H C P N : BHist) : LocatedMetricUp
  deriving DecidableEq

def locatedMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedMetricEncodeBHist h

def locatedMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedMetricDecodeBHist tail)

private theorem LocatedMetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedMetricDecodeBHist (locatedMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedMetricFields : LocatedMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedMetricUp.mk X M D S R E Z H C P N => [X, M, D, S, R, E, Z, H, C, P, N]

def locatedMetricToEventFlow : LocatedMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedMetricFields x).map locatedMetricEncodeBHist

private def LocatedMetricTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LocatedMetricTasteGate_single_carrier_alignment_eventAt index rest

def locatedMetricFromEventFlow (ef : EventFlow) : Option LocatedMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedMetricUp.mk
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 0 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 1 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 2 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 3 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 4 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 5 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 6 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 7 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 8 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 9 ef))
      (locatedMetricDecodeBHist (LocatedMetricTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem LocatedMetricTasteGate_single_carrier_alignment_round_trip
    (x : LocatedMetricUp) :
    locatedMetricFromEventFlow (locatedMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X M D S R E Z H C P N =>
      change
        some
          (LocatedMetricUp.mk
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist X))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist M))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist D))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist S))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist R))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist E))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist Z))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist H))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist C))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist P))
            (locatedMetricDecodeBHist (locatedMetricEncodeBHist N))) =
          some (LocatedMetricUp.mk X M D S R E Z H C P N)
      rw [LocatedMetricTasteGate_single_carrier_alignment_decode_encode X,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode M,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode D,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode S,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode R,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode E,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode Z,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode H,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode C,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode P,
        LocatedMetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedMetricUp} :
    locatedMetricToEventFlow x = locatedMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedMetricFromEventFlow (locatedMetricToEventFlow x) =
        locatedMetricFromEventFlow (locatedMetricToEventFlow y) :=
    congrArg locatedMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedMetricTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedMetricUp, locatedMetricFields x = locatedMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ M₁ D₁ S₁ R₁ E₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ M₂ D₂ S₂ R₂ E₂ Z₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedMetricBHistCarrier : BHistCarrier LocatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedMetricToEventFlow
  fromEventFlow := locatedMetricFromEventFlow

instance locatedMetricChapterTasteGate : ChapterTasteGate LocatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedMetricFromEventFlow (locatedMetricToEventFlow x) = some x
    exact LocatedMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedMetricDecodeBHist (locatedMetricEncodeBHist h) = h) ∧
      (∀ x : LocatedMetricUp,
        locatedMetricFromEventFlow (locatedMetricToEventFlow x) = some x) ∧
        (∀ x y : LocatedMetricUp,
          locatedMetricToEventFlow x = locatedMetricToEventFlow y → x = y) ∧
          locatedMetricEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : LocatedMetricUp, locatedMetricFields x = locatedMetricFields y → x = y) ∧
              (∃ x y : LocatedMetricUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedMetricTasteGate_single_carrier_alignment_decode_encode,
      LocatedMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LocatedMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      LocatedMetricTasteGate_single_carrier_alignment_fields_faithful,
      ⟨LocatedMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        LocatedMetricUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.LocatedMetricUp
