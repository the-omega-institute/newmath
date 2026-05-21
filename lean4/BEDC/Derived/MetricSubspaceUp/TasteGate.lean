import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricSubspaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricSubspaceUp : Type where
  | mk (X A D H C P N : BHist) : MetricSubspaceUp
  deriving DecidableEq

def metricSubspaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricSubspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricSubspaceEncodeBHist h

def metricSubspaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricSubspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricSubspaceDecodeBHist tail)

private theorem metricSubspace_decode_encode_bhist :
    ∀ h : BHist, metricSubspaceDecodeBHist (metricSubspaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metricSubspaceFields : MetricSubspaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricSubspaceUp.mk X A D H C P N => [X, A, D, H, C, P, N]

def metricSubspaceToEventFlow : MetricSubspaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricSubspaceUp.mk X A D H C P N =>
      [metricSubspaceEncodeBHist X,
        metricSubspaceEncodeBHist A,
        metricSubspaceEncodeBHist D,
        metricSubspaceEncodeBHist H,
        metricSubspaceEncodeBHist C,
        metricSubspaceEncodeBHist P,
        metricSubspaceEncodeBHist N]

private def metricSubspaceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => metricSubspaceRawAt n rest

private def metricSubspaceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => metricSubspaceLengthEq n rest

def metricSubspaceFromEventFlow : EventFlow → Option MetricSubspaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match metricSubspaceLengthEq 7 flow with
      | true =>
          some
            (MetricSubspaceUp.mk
              (metricSubspaceDecodeBHist (metricSubspaceRawAt 0 flow))
              (metricSubspaceDecodeBHist (metricSubspaceRawAt 1 flow))
              (metricSubspaceDecodeBHist (metricSubspaceRawAt 2 flow))
              (metricSubspaceDecodeBHist (metricSubspaceRawAt 3 flow))
              (metricSubspaceDecodeBHist (metricSubspaceRawAt 4 flow))
              (metricSubspaceDecodeBHist (metricSubspaceRawAt 5 flow))
              (metricSubspaceDecodeBHist (metricSubspaceRawAt 6 flow)))
      | false => none

private theorem metricSubspace_round_trip :
    ∀ x : MetricSubspaceUp,
      metricSubspaceFromEventFlow (metricSubspaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A D H C P N =>
      change
        some
          (MetricSubspaceUp.mk
            (metricSubspaceDecodeBHist (metricSubspaceEncodeBHist X))
            (metricSubspaceDecodeBHist (metricSubspaceEncodeBHist A))
            (metricSubspaceDecodeBHist (metricSubspaceEncodeBHist D))
            (metricSubspaceDecodeBHist (metricSubspaceEncodeBHist H))
            (metricSubspaceDecodeBHist (metricSubspaceEncodeBHist C))
            (metricSubspaceDecodeBHist (metricSubspaceEncodeBHist P))
            (metricSubspaceDecodeBHist (metricSubspaceEncodeBHist N))) =
          some (MetricSubspaceUp.mk X A D H C P N)
      rw [metricSubspace_decode_encode_bhist X,
        metricSubspace_decode_encode_bhist A,
        metricSubspace_decode_encode_bhist D,
        metricSubspace_decode_encode_bhist H,
        metricSubspace_decode_encode_bhist C,
        metricSubspace_decode_encode_bhist P,
        metricSubspace_decode_encode_bhist N]

private theorem metricSubspaceToEventFlow_injective {x y : MetricSubspaceUp} :
    metricSubspaceToEventFlow x = metricSubspaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricSubspaceFromEventFlow (metricSubspaceToEventFlow x) =
        metricSubspaceFromEventFlow (metricSubspaceToEventFlow y) :=
    congrArg metricSubspaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricSubspace_round_trip x).symm
      (Eq.trans hread (metricSubspace_round_trip y)))

private theorem metricSubspace_field_faithful :
    ∀ x y : MetricSubspaceUp,
      metricSubspaceFields x = metricSubspaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X1 A1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 A2 D2 H2 C2 P2 N2 =>
          cases h
          rfl

instance metricSubspaceBHistCarrier : BHistCarrier MetricSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricSubspaceToEventFlow
  fromEventFlow := metricSubspaceFromEventFlow

instance metricSubspaceChapterTasteGate : ChapterTasteGate MetricSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricSubspaceFromEventFlow (metricSubspaceToEventFlow x) = some x
    exact metricSubspace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricSubspaceToEventFlow_injective heq)

instance metricSubspaceFieldFaithful : FieldFaithful MetricSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricSubspaceFields
  field_faithful := metricSubspace_field_faithful

instance metricSubspaceNontrivial : Nontrivial MetricSubspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricSubspaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      MetricSubspaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricSubspaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricSubspaceChapterTasteGate

theorem MetricSubspaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricSubspaceDecodeBHist (metricSubspaceEncodeBHist h) = h) ∧
      metricSubspaceFields
          (MetricSubspaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨metricSubspace_decode_encode_bhist, rfl⟩

end BEDC.Derived.MetricSubspaceUp
