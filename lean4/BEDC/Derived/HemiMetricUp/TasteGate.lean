import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HemiMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HemiMetricUp : Type where
  | mk (S X D Z T B Q L M U R K C P N : BHist) : HemiMetricUp
  deriving DecidableEq

def hemiMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hemiMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hemiMetricEncodeBHist h

def hemiMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hemiMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hemiMetricDecodeBHist tail)

private theorem HemiMetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hemiMetricDecodeBHist (hemiMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hemiMetricFields : HemiMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HemiMetricUp.mk S X D Z T B Q L M U R K C P N =>
      [S, X, D, Z, T, B, Q, L, M, U, R, K, C, P, N]

def hemiMetricToEventFlow : HemiMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hemiMetricFields x).map hemiMetricEncodeBHist

private def hemiMetricEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hemiMetricEventAt index rest

def hemiMetricFromEventFlow (ef : EventFlow) : Option HemiMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HemiMetricUp.mk
      (hemiMetricDecodeBHist (hemiMetricEventAt 0 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 1 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 2 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 3 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 4 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 5 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 6 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 7 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 8 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 9 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 10 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 11 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 12 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 13 ef))
      (hemiMetricDecodeBHist (hemiMetricEventAt 14 ef)))

private theorem HemiMetricTasteGate_single_carrier_alignment_round_trip
    (x : HemiMetricUp) :
    hemiMetricFromEventFlow (hemiMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S X D Z T B Q L M U R K C P N =>
      change
        some
          (HemiMetricUp.mk
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist S))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist X))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist D))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist Z))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist T))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist B))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist Q))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist L))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist M))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist U))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist R))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist K))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist C))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist P))
            (hemiMetricDecodeBHist (hemiMetricEncodeBHist N))) =
          some (HemiMetricUp.mk S X D Z T B Q L M U R K C P N)
      rw [HemiMetricTasteGate_single_carrier_alignment_decode_encode S,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode X,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode D,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode Z,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode T,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode B,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode Q,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode L,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode M,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode U,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode R,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode K,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode C,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode P,
        HemiMetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem HemiMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HemiMetricUp} :
    hemiMetricToEventFlow x = hemiMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hemiMetricFromEventFlow (hemiMetricToEventFlow x) =
        hemiMetricFromEventFlow (hemiMetricToEventFlow y) :=
    congrArg hemiMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HemiMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HemiMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem HemiMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : HemiMetricUp, hemiMetricFields x = hemiMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ X₁ D₁ Z₁ T₁ B₁ Q₁ L₁ M₁ U₁ R₁ K₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ X₂ D₂ Z₂ T₂ B₂ Q₂ L₂ M₂ U₂ R₂ K₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance hemiMetricBHistCarrier : BHistCarrier HemiMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hemiMetricToEventFlow
  fromEventFlow := hemiMetricFromEventFlow

instance hemiMetricChapterTasteGate : ChapterTasteGate HemiMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hemiMetricFromEventFlow (hemiMetricToEventFlow x) = some x
    exact HemiMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HemiMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hemiMetricFieldFaithful : FieldFaithful HemiMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hemiMetricFields
  field_faithful := HemiMetricTasteGate_single_carrier_alignment_fields

instance hemiMetricNontrivial : Nontrivial HemiMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HemiMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HemiMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def HemiMetricTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HemiMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hemiMetricChapterTasteGate

theorem HemiMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, hemiMetricDecodeBHist (hemiMetricEncodeBHist h) = h) ∧
      (∀ x : HemiMetricUp, hemiMetricFromEventFlow (hemiMetricToEventFlow x) = some x) ∧
        (∀ x y : HemiMetricUp, hemiMetricToEventFlow x = hemiMetricToEventFlow y → x = y) ∧
          hemiMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨HemiMetricTasteGate_single_carrier_alignment_decode_encode,
      HemiMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HemiMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HemiMetricUp
