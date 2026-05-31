import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricSubspaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactMetricSubspaceUp : Type where
  | mk (S K T L W R E H C P N : BHist) : CompactMetricSubspaceUp
  deriving DecidableEq

def compactMetricSubspaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactMetricSubspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactMetricSubspaceEncodeBHist h

def compactMetricSubspaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactMetricSubspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactMetricSubspaceDecodeBHist tail)

private theorem CompactMetricSubspaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactMetricSubspaceFields : CompactMetricSubspaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricSubspaceUp.mk S K T L W R E H C P N => [S, K, T, L, W, R, E, H, C, P, N]

def compactMetricSubspaceToEventFlow : CompactMetricSubspaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactMetricSubspaceFields x).map compactMetricSubspaceEncodeBHist

private def compactMetricSubspaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactMetricSubspaceEventAtDefault index rest

def compactMetricSubspaceFromEventFlow (ef : EventFlow) : Option CompactMetricSubspaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactMetricSubspaceUp.mk
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 0 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 1 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 2 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 3 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 4 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 5 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 6 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 7 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 8 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 9 ef))
      (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEventAtDefault 10 ef)))

def compactMetricSubspaceFromEventFlow_round_trip :
    ∀ x : CompactMetricSubspaceUp,
      compactMetricSubspaceFromEventFlow (compactMetricSubspaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S K T L W R E H C P N =>
      change
        some
          (CompactMetricSubspaceUp.mk
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist S))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist K))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist T))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist L))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist W))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist R))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist E))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist H))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist C))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist P))
            (compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist N))) =
          some (CompactMetricSubspaceUp.mk S K T L W R E H C P N)
      rw [CompactMetricSubspaceTasteGate_single_carrier_alignment_decode S,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode K,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode T,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode L,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode W,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode R,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode E,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode H,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode C,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode P,
        CompactMetricSubspaceTasteGate_single_carrier_alignment_decode N]

def compactMetricSubspaceToEventFlow_injective
    {x y : CompactMetricSubspaceUp} :
    compactMetricSubspaceToEventFlow x = compactMetricSubspaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactMetricSubspaceFromEventFlow (compactMetricSubspaceToEventFlow x) =
        compactMetricSubspaceFromEventFlow (compactMetricSubspaceToEventFlow y) :=
    congrArg compactMetricSubspaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (compactMetricSubspaceFromEventFlow_round_trip x).symm
      (Eq.trans hread (compactMetricSubspaceFromEventFlow_round_trip y)))

private theorem CompactMetricSubspaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompactMetricSubspaceUp,
      compactMetricSubspaceFields x = compactMetricSubspaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 K1 T1 L1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 K2 T2 L2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactMetricSubspaceBHistCarrier : BHistCarrier CompactMetricSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactMetricSubspaceToEventFlow
  fromEventFlow := compactMetricSubspaceFromEventFlow

instance compactMetricSubspaceChapterTasteGate : ChapterTasteGate CompactMetricSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactMetricSubspaceFromEventFlow (compactMetricSubspaceToEventFlow x) = some x
    exact compactMetricSubspaceFromEventFlow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactMetricSubspaceToEventFlow_injective heq)

instance compactMetricSubspaceFieldFaithful : FieldFaithful CompactMetricSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactMetricSubspaceFields
  field_faithful := CompactMetricSubspaceTasteGate_single_carrier_alignment_fields

instance compactMetricSubspaceNontrivial : Nontrivial CompactMetricSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactMetricSubspaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompactMetricSubspaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactMetricSubspaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactMetricSubspaceChapterTasteGate

theorem CompactMetricSubspaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactMetricSubspaceUp) ∧
      Nonempty (FieldFaithful CompactMetricSubspaceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactMetricSubspaceUp) ∧
          (∀ h : BHist,
            compactMetricSubspaceDecodeBHist (compactMetricSubspaceEncodeBHist h) = h) ∧
            (∀ x : CompactMetricSubspaceUp,
              compactMetricSubspaceFromEventFlow
                  (compactMetricSubspaceToEventFlow x) = some x) ∧
              (∀ x y : CompactMetricSubspaceUp,
                compactMetricSubspaceToEventFlow x = compactMetricSubspaceToEventFlow y →
                  x = y) ∧
                compactMetricSubspaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨compactMetricSubspaceChapterTasteGate⟩,
      ⟨compactMetricSubspaceFieldFaithful⟩,
      ⟨compactMetricSubspaceNontrivial⟩,
      CompactMetricSubspaceTasteGate_single_carrier_alignment_decode,
      compactMetricSubspaceFromEventFlow_round_trip,
      (fun _ _ heq => compactMetricSubspaceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactMetricSubspaceUp.TasteGate
