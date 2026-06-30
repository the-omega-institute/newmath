import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeaklyLocatedIntervalSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeaklyLocatedIntervalSelectionUp : Type where
  | mk (L Q D W R E H C P N : BHist) : WeaklyLocatedIntervalSelectionUp
  deriving DecidableEq

def weaklyLocatedIntervalSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weaklyLocatedIntervalSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weaklyLocatedIntervalSelectionEncodeBHist h

def weaklyLocatedIntervalSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weaklyLocatedIntervalSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weaklyLocatedIntervalSelectionDecodeBHist tail)

private theorem WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      weaklyLocatedIntervalSelectionDecodeBHist
        (weaklyLocatedIntervalSelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def weaklyLocatedIntervalSelectionFields : WeaklyLocatedIntervalSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeaklyLocatedIntervalSelectionUp.mk L Q D W R E H C P N => [L, Q, D, W, R, E, H, C, P, N]

def weaklyLocatedIntervalSelectionToEventFlow : WeaklyLocatedIntervalSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (weaklyLocatedIntervalSelectionFields x).map weaklyLocatedIntervalSelectionEncodeBHist

private def weaklyLocatedIntervalSelectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => weaklyLocatedIntervalSelectionEventAtDefault index rest

def weaklyLocatedIntervalSelectionFromEventFlow :
    EventFlow → Option WeaklyLocatedIntervalSelectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (WeaklyLocatedIntervalSelectionUp.mk
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 0 ef))
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 1 ef))
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 2 ef))
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 3 ef))
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 4 ef))
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 5 ef))
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 6 ef))
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 7 ef))
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 8 ef))
          (weaklyLocatedIntervalSelectionDecodeBHist
            (weaklyLocatedIntervalSelectionEventAtDefault 9 ef)))

private theorem WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : WeaklyLocatedIntervalSelectionUp,
      weaklyLocatedIntervalSelectionFromEventFlow
        (weaklyLocatedIntervalSelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L Q D W R E H C P N =>
      change
        some
          (WeaklyLocatedIntervalSelectionUp.mk
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist L))
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist Q))
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist D))
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist W))
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist R))
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist E))
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist H))
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist C))
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist P))
            (weaklyLocatedIntervalSelectionDecodeBHist
              (weaklyLocatedIntervalSelectionEncodeBHist N))) =
          some (WeaklyLocatedIntervalSelectionUp.mk L Q D W R E H C P N)
      rw [WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode L,
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode Q,
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode D,
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode W,
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode R,
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode E,
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode H,
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode C,
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode P,
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode N]

private theorem WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WeaklyLocatedIntervalSelectionUp} :
    weaklyLocatedIntervalSelectionToEventFlow x = weaklyLocatedIntervalSelectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weaklyLocatedIntervalSelectionFromEventFlow
          (weaklyLocatedIntervalSelectionToEventFlow x) =
        weaklyLocatedIntervalSelectionFromEventFlow
          (weaklyLocatedIntervalSelectionToEventFlow y) :=
    congrArg weaklyLocatedIntervalSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_fields :
    ∀ x y : WeaklyLocatedIntervalSelectionUp,
      weaklyLocatedIntervalSelectionFields x = weaklyLocatedIntervalSelectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ Q₁ D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ Q₂ D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance weaklyLocatedIntervalSelectionBHistCarrier :
    BHistCarrier WeaklyLocatedIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weaklyLocatedIntervalSelectionToEventFlow
  fromEventFlow := weaklyLocatedIntervalSelectionFromEventFlow

instance weaklyLocatedIntervalSelectionChapterTasteGate :
    ChapterTasteGate WeaklyLocatedIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      weaklyLocatedIntervalSelectionFromEventFlow
        (weaklyLocatedIntervalSelectionToEventFlow x) = some x
    exact WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance weaklyLocatedIntervalSelectionFieldFaithful :
    FieldFaithful WeaklyLocatedIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := weaklyLocatedIntervalSelectionFields
  field_faithful := WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_fields

instance weaklyLocatedIntervalSelectionNontrivial : Nontrivial WeaklyLocatedIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WeaklyLocatedIntervalSelectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WeaklyLocatedIntervalSelectionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WeaklyLocatedIntervalSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weaklyLocatedIntervalSelectionChapterTasteGate

theorem WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      weaklyLocatedIntervalSelectionDecodeBHist
        (weaklyLocatedIntervalSelectionEncodeBHist h) = h) ∧
      (∀ x : WeaklyLocatedIntervalSelectionUp,
        weaklyLocatedIntervalSelectionFromEventFlow
          (weaklyLocatedIntervalSelectionToEventFlow x) = some x) ∧
        (∀ x y : WeaklyLocatedIntervalSelectionUp,
          weaklyLocatedIntervalSelectionToEventFlow x =
            weaklyLocatedIntervalSelectionToEventFlow y → x = y) ∧
          weaklyLocatedIntervalSelectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_decode,
      WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        WeaklyLocatedIntervalSelectionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.WeaklyLocatedIntervalSelectionUp
