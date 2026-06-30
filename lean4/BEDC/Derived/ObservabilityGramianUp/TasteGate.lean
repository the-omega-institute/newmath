import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservabilityGramianUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservabilityGramianUp : Type where
  | mk (A C n W L R P N : BHist) : ObservabilityGramianUp
  deriving DecidableEq

def observabilityGramianEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observabilityGramianEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observabilityGramianEncodeBHist h

def observabilityGramianDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observabilityGramianDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observabilityGramianDecodeBHist tail)

private theorem ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      observabilityGramianDecodeBHist (observabilityGramianEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observabilityGramianFields : ObservabilityGramianUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObservabilityGramianUp.mk A C n W L R P N => [A, C, n, W, L, R, P, N]

def observabilityGramianToEventFlow : ObservabilityGramianUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (observabilityGramianFields x).map observabilityGramianEncodeBHist

private def observabilityGramianEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => observabilityGramianEventAt index rest

def observabilityGramianFromEventFlow (ef : EventFlow) : Option ObservabilityGramianUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ObservabilityGramianUp.mk
      (observabilityGramianDecodeBHist (observabilityGramianEventAt 0 ef))
      (observabilityGramianDecodeBHist (observabilityGramianEventAt 1 ef))
      (observabilityGramianDecodeBHist (observabilityGramianEventAt 2 ef))
      (observabilityGramianDecodeBHist (observabilityGramianEventAt 3 ef))
      (observabilityGramianDecodeBHist (observabilityGramianEventAt 4 ef))
      (observabilityGramianDecodeBHist (observabilityGramianEventAt 5 ef))
      (observabilityGramianDecodeBHist (observabilityGramianEventAt 6 ef))
      (observabilityGramianDecodeBHist (observabilityGramianEventAt 7 ef)))

private theorem ObservabilityGramianTasteGate_single_carrier_alignment_round_trip
    (x : ObservabilityGramianUp) :
    observabilityGramianFromEventFlow (observabilityGramianToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A C n W L R P N =>
      change
        some
          (ObservabilityGramianUp.mk
            (observabilityGramianDecodeBHist (observabilityGramianEncodeBHist A))
            (observabilityGramianDecodeBHist (observabilityGramianEncodeBHist C))
            (observabilityGramianDecodeBHist (observabilityGramianEncodeBHist n))
            (observabilityGramianDecodeBHist (observabilityGramianEncodeBHist W))
            (observabilityGramianDecodeBHist (observabilityGramianEncodeBHist L))
            (observabilityGramianDecodeBHist (observabilityGramianEncodeBHist R))
            (observabilityGramianDecodeBHist (observabilityGramianEncodeBHist P))
            (observabilityGramianDecodeBHist (observabilityGramianEncodeBHist N))) =
          some (ObservabilityGramianUp.mk A C n W L R P N)
      rw [ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode A,
        ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode C,
        ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode n,
        ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode W,
        ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode L,
        ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode R,
        ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode P,
        ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode N]

private theorem ObservabilityGramianTasteGate_single_carrier_alignment_injective
    {x y : ObservabilityGramianUp} :
    observabilityGramianToEventFlow x = observabilityGramianToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observabilityGramianFromEventFlow (observabilityGramianToEventFlow x) =
        observabilityGramianFromEventFlow (observabilityGramianToEventFlow y) :=
    congrArg observabilityGramianFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ObservabilityGramianTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ObservabilityGramianTasteGate_single_carrier_alignment_round_trip y)))

private theorem observabilityGramianFields_injective :
    ∀ x y : ObservabilityGramianUp,
      observabilityGramianFields x = observabilityGramianFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ C₁ n₁ W₁ L₁ R₁ P₁ N₁ =>
      cases y with
      | mk A₂ C₂ n₂ W₂ L₂ R₂ P₂ N₂ =>
          cases hfields
          rfl

instance observabilityGramianBHistCarrier : BHistCarrier ObservabilityGramianUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observabilityGramianToEventFlow
  fromEventFlow := observabilityGramianFromEventFlow

instance observabilityGramianChapterTasteGate :
    ChapterTasteGate ObservabilityGramianUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observabilityGramianFromEventFlow (observabilityGramianToEventFlow x) =
      some x
    exact ObservabilityGramianTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ObservabilityGramianTasteGate_single_carrier_alignment_injective heq)

instance observabilityGramianFieldFaithful : FieldFaithful ObservabilityGramianUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observabilityGramianFields
  field_faithful := observabilityGramianFields_injective

instance observabilityGramianNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ObservabilityGramianUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObservabilityGramianUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObservabilityGramianUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ObservabilityGramianTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ObservabilityGramianUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observabilityGramianChapterTasteGate

theorem ObservabilityGramianTasteGate_single_carrier_alignment :
    (∀ h : BHist, observabilityGramianDecodeBHist (observabilityGramianEncodeBHist h) = h) ∧
      observabilityGramianEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x : ObservabilityGramianUp,
          observabilityGramianFromEventFlow (observabilityGramianToEventFlow x) = some x) ∧
          (∀ x y : ObservabilityGramianUp,
            observabilityGramianToEventFlow x = observabilityGramianToEventFlow y → x = y) ∧
            (∃ x y : ObservabilityGramianUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ObservabilityGramianTasteGate_single_carrier_alignment_decode_encode
  constructor
  · rfl
  constructor
  · exact ObservabilityGramianTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact ObservabilityGramianTasteGate_single_carrier_alignment_injective heq
  · exact
      ⟨ObservabilityGramianUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        ObservabilityGramianUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩

end BEDC.Derived.ObservabilityGramianUp
