import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealMetricUp : Type where
  | mk (X Y A D S R H C P N : BHist) : RealMetricUp
  deriving DecidableEq

def realMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realMetricEncodeBHist h

def realMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realMetricDecodeBHist tail)

private theorem RealMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realMetricDecodeBHist (realMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realMetricFields : RealMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealMetricUp.mk X Y A D S R H C P N => [X, Y, A, D, S, R, H, C, P, N]

def realMetricToEventFlow : RealMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realMetricFields x).map realMetricEncodeBHist

private def realMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realMetricEventAtDefault index rest

def realMetricFromEventFlow (ef : EventFlow) : Option RealMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealMetricUp.mk
      (realMetricDecodeBHist (realMetricEventAtDefault 0 ef))
      (realMetricDecodeBHist (realMetricEventAtDefault 1 ef))
      (realMetricDecodeBHist (realMetricEventAtDefault 2 ef))
      (realMetricDecodeBHist (realMetricEventAtDefault 3 ef))
      (realMetricDecodeBHist (realMetricEventAtDefault 4 ef))
      (realMetricDecodeBHist (realMetricEventAtDefault 5 ef))
      (realMetricDecodeBHist (realMetricEventAtDefault 6 ef))
      (realMetricDecodeBHist (realMetricEventAtDefault 7 ef))
      (realMetricDecodeBHist (realMetricEventAtDefault 8 ef))
      (realMetricDecodeBHist (realMetricEventAtDefault 9 ef)))

private theorem RealMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealMetricUp,
      realMetricFromEventFlow (realMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y A D S R H C P N =>
      change
        some
          (RealMetricUp.mk
            (realMetricDecodeBHist (realMetricEncodeBHist X))
            (realMetricDecodeBHist (realMetricEncodeBHist Y))
            (realMetricDecodeBHist (realMetricEncodeBHist A))
            (realMetricDecodeBHist (realMetricEncodeBHist D))
            (realMetricDecodeBHist (realMetricEncodeBHist S))
            (realMetricDecodeBHist (realMetricEncodeBHist R))
            (realMetricDecodeBHist (realMetricEncodeBHist H))
            (realMetricDecodeBHist (realMetricEncodeBHist C))
            (realMetricDecodeBHist (realMetricEncodeBHist P))
            (realMetricDecodeBHist (realMetricEncodeBHist N))) =
          some (RealMetricUp.mk X Y A D S R H C P N)
      rw [RealMetricTasteGate_single_carrier_alignment_decode X,
        RealMetricTasteGate_single_carrier_alignment_decode Y,
        RealMetricTasteGate_single_carrier_alignment_decode A,
        RealMetricTasteGate_single_carrier_alignment_decode D,
        RealMetricTasteGate_single_carrier_alignment_decode S,
        RealMetricTasteGate_single_carrier_alignment_decode R,
        RealMetricTasteGate_single_carrier_alignment_decode H,
        RealMetricTasteGate_single_carrier_alignment_decode C,
        RealMetricTasteGate_single_carrier_alignment_decode P,
        RealMetricTasteGate_single_carrier_alignment_decode N]

private theorem RealMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealMetricUp} :
    realMetricToEventFlow x = realMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realMetricFromEventFlow (realMetricToEventFlow x) =
        realMetricFromEventFlow (realMetricToEventFlow y) :=
    congrArg realMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealMetricUp, realMetricFields x = realMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 A1 D1 S1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 A2 D2 S2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realMetricBHistCarrier : BHistCarrier RealMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realMetricToEventFlow
  fromEventFlow := realMetricFromEventFlow

instance realMetricChapterTasteGate : ChapterTasteGate RealMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realMetricFromEventFlow (realMetricToEventFlow x) = some x
    exact RealMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realMetricFieldFaithful : FieldFaithful RealMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realMetricFields
  field_faithful := RealMetricTasteGate_single_carrier_alignment_fields

instance realMetricNontrivial : Nontrivial RealMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realMetricChapterTasteGate

theorem RealMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, realMetricDecodeBHist (realMetricEncodeBHist h) = h) ∧
      (∀ x : RealMetricUp, realMetricFromEventFlow (realMetricToEventFlow x) = some x) ∧
        (∀ x y : RealMetricUp, realMetricToEventFlow x = realMetricToEventFlow y → x = y) ∧
          realMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealMetricTasteGate_single_carrier_alignment_decode,
      RealMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealMetricUp
