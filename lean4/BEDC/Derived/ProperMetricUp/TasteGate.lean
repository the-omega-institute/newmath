import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProperMetricUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProperMetricUp : Type where
  | mk (X B K L T H C Q N : BHist) : ProperMetricUp
  deriving DecidableEq

def properMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: properMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: properMetricEncodeBHist h

def properMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (properMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (properMetricDecodeBHist tail)

private theorem ProperMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, properMetricDecodeBHist (properMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def properMetricFields : ProperMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProperMetricUp.mk X B K L T H C Q N => [X, B, K, L, T, H, C, Q, N]

def properMetricToEventFlow : ProperMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (properMetricFields x).map properMetricEncodeBHist

private def properMetricEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => properMetricEventAt index rest

def properMetricFromEventFlow (ef : EventFlow) : Option ProperMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProperMetricUp.mk
      (properMetricDecodeBHist (properMetricEventAt 0 ef))
      (properMetricDecodeBHist (properMetricEventAt 1 ef))
      (properMetricDecodeBHist (properMetricEventAt 2 ef))
      (properMetricDecodeBHist (properMetricEventAt 3 ef))
      (properMetricDecodeBHist (properMetricEventAt 4 ef))
      (properMetricDecodeBHist (properMetricEventAt 5 ef))
      (properMetricDecodeBHist (properMetricEventAt 6 ef))
      (properMetricDecodeBHist (properMetricEventAt 7 ef))
      (properMetricDecodeBHist (properMetricEventAt 8 ef)))

private theorem ProperMetricTasteGate_single_carrier_alignment_round_trip
    (x : ProperMetricUp) :
    properMetricFromEventFlow (properMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X B K L T H C Q N =>
      change
        some
          (ProperMetricUp.mk
            (properMetricDecodeBHist (properMetricEncodeBHist X))
            (properMetricDecodeBHist (properMetricEncodeBHist B))
            (properMetricDecodeBHist (properMetricEncodeBHist K))
            (properMetricDecodeBHist (properMetricEncodeBHist L))
            (properMetricDecodeBHist (properMetricEncodeBHist T))
            (properMetricDecodeBHist (properMetricEncodeBHist H))
            (properMetricDecodeBHist (properMetricEncodeBHist C))
            (properMetricDecodeBHist (properMetricEncodeBHist Q))
            (properMetricDecodeBHist (properMetricEncodeBHist N))) =
          some (ProperMetricUp.mk X B K L T H C Q N)
      rw [ProperMetricTasteGate_single_carrier_alignment_decode X,
        ProperMetricTasteGate_single_carrier_alignment_decode B,
        ProperMetricTasteGate_single_carrier_alignment_decode K,
        ProperMetricTasteGate_single_carrier_alignment_decode L,
        ProperMetricTasteGate_single_carrier_alignment_decode T,
        ProperMetricTasteGate_single_carrier_alignment_decode H,
        ProperMetricTasteGate_single_carrier_alignment_decode C,
        ProperMetricTasteGate_single_carrier_alignment_decode Q,
        ProperMetricTasteGate_single_carrier_alignment_decode N]

private theorem ProperMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ProperMetricUp} :
    properMetricToEventFlow x = properMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      properMetricFromEventFlow (properMetricToEventFlow x) =
        properMetricFromEventFlow (properMetricToEventFlow y) :=
    congrArg properMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ProperMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProperMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProperMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : ProperMetricUp, properMetricFields x = properMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 B1 K1 L1 T1 H1 C1 Q1 N1 =>
      cases y with
      | mk X2 B2 K2 L2 T2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance properMetricBHistCarrier : BHistCarrier ProperMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := properMetricToEventFlow
  fromEventFlow := properMetricFromEventFlow

instance properMetricChapterTasteGate : ChapterTasteGate ProperMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change properMetricFromEventFlow (properMetricToEventFlow x) = some x
    exact ProperMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProperMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance properMetricFieldFaithful : FieldFaithful ProperMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := properMetricFields
  field_faithful := ProperMetricTasteGate_single_carrier_alignment_fields

instance properMetricNontrivial : BEDC.Meta.TasteGate.Nontrivial ProperMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProperMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProperMetricUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ProperMetricTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ProperMetricUp) ∧
      Nonempty (FieldFaithful ProperMetricUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial ProperMetricUp) ∧
      (∀ h : BHist, properMetricDecodeBHist (properMetricEncodeBHist h) = h) ∧
      (∀ x : ProperMetricUp, properMetricFromEventFlow (properMetricToEventFlow x) = some x) ∧
      properMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨properMetricChapterTasteGate⟩,
      ⟨properMetricFieldFaithful⟩,
      ⟨properMetricNontrivial⟩,
      ProperMetricTasteGate_single_carrier_alignment_decode,
      ProperMetricTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.ProperMetricUp.TasteGate
