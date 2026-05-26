import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotallyBoundedMetricUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotallyBoundedMetricUp : Type where
  | mk (M R E D S Q H C P N : BHist) : TotallyBoundedMetricUp
  deriving DecidableEq

def totallyBoundedMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totallyBoundedMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totallyBoundedMetricEncodeBHist h

def totallyBoundedMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totallyBoundedMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totallyBoundedMetricDecodeBHist tail)

private theorem TotallyBoundedMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def totallyBoundedMetricToEventFlow : TotallyBoundedMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TotallyBoundedMetricUp.mk M R E D S Q H C P N =>
      [[BMark.b0],
        totallyBoundedMetricEncodeBHist M,
        [BMark.b1, BMark.b0],
        totallyBoundedMetricEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedMetricEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedMetricEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedMetricEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedMetricEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedMetricEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        totallyBoundedMetricEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        totallyBoundedMetricEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedMetricEncodeBHist N]

private def totallyBoundedMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => totallyBoundedMetricEventAtDefault index rest

def totallyBoundedMetricFromEventFlow (ef : EventFlow) : Option TotallyBoundedMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TotallyBoundedMetricUp.mk
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 1 ef))
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 3 ef))
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 5 ef))
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 7 ef))
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 9 ef))
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 11 ef))
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 13 ef))
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 15 ef))
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 17 ef))
      (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEventAtDefault 19 ef)))

private theorem TotallyBoundedMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TotallyBoundedMetricUp,
      totallyBoundedMetricFromEventFlow (totallyBoundedMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M R E D S Q H C P N =>
      change
        some
          (TotallyBoundedMetricUp.mk
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist M))
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist R))
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist E))
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist D))
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist S))
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist Q))
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist H))
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist C))
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist P))
            (totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist N))) =
          some (TotallyBoundedMetricUp.mk M R E D S Q H C P N)
      rw [TotallyBoundedMetricTasteGate_single_carrier_alignment_decode M,
        TotallyBoundedMetricTasteGate_single_carrier_alignment_decode R,
        TotallyBoundedMetricTasteGate_single_carrier_alignment_decode E,
        TotallyBoundedMetricTasteGate_single_carrier_alignment_decode D,
        TotallyBoundedMetricTasteGate_single_carrier_alignment_decode S,
        TotallyBoundedMetricTasteGate_single_carrier_alignment_decode Q,
        TotallyBoundedMetricTasteGate_single_carrier_alignment_decode H,
        TotallyBoundedMetricTasteGate_single_carrier_alignment_decode C,
        TotallyBoundedMetricTasteGate_single_carrier_alignment_decode P,
        TotallyBoundedMetricTasteGate_single_carrier_alignment_decode N]

private theorem TotallyBoundedMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TotallyBoundedMetricUp} :
    totallyBoundedMetricToEventFlow x = totallyBoundedMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totallyBoundedMetricFromEventFlow (totallyBoundedMetricToEventFlow x) =
        totallyBoundedMetricFromEventFlow (totallyBoundedMetricToEventFlow y) :=
    congrArg totallyBoundedMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TotallyBoundedMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TotallyBoundedMetricTasteGate_single_carrier_alignment_round_trip y)))

private def totallyBoundedMetricFields : TotallyBoundedMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TotallyBoundedMetricUp.mk M R E D S Q H C P N => [M, R, E, D, S, Q, H, C, P, N]

private theorem TotallyBoundedMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : TotallyBoundedMetricUp, totallyBoundedMetricFields x = totallyBoundedMetricFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 R1 E1 D1 S1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 R2 E2 D2 S2 Q2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance totallyBoundedMetricBHistCarrier : BHistCarrier TotallyBoundedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totallyBoundedMetricToEventFlow
  fromEventFlow := totallyBoundedMetricFromEventFlow

instance totallyBoundedMetricChapterTasteGate : ChapterTasteGate TotallyBoundedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change totallyBoundedMetricFromEventFlow (totallyBoundedMetricToEventFlow x) = some x
    exact TotallyBoundedMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TotallyBoundedMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance totallyBoundedMetricFieldFaithful : FieldFaithful TotallyBoundedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := totallyBoundedMetricFields
  field_faithful := TotallyBoundedMetricTasteGate_single_carrier_alignment_fields

instance totallyBoundedMetricNontrivial : Nontrivial TotallyBoundedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TotallyBoundedMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TotallyBoundedMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def totallyBoundedMetricTasteGate : ChapterTasteGate TotallyBoundedMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  totallyBoundedMetricChapterTasteGate

theorem TotallyBoundedMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, totallyBoundedMetricDecodeBHist (totallyBoundedMetricEncodeBHist h) = h) ∧
      (∀ x : TotallyBoundedMetricUp,
        totallyBoundedMetricFromEventFlow (totallyBoundedMetricToEventFlow x) = some x) ∧
        (∀ x y : TotallyBoundedMetricUp,
          totallyBoundedMetricToEventFlow x = totallyBoundedMetricToEventFlow y → x = y) ∧
          totallyBoundedMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨TotallyBoundedMetricTasteGate_single_carrier_alignment_decode,
      TotallyBoundedMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => TotallyBoundedMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.TotallyBoundedMetricUp.TasteGate
