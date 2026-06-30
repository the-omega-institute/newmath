import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedLinearFunctionalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedLinearFunctionalUp : Type where
  | mk (E L T K O H C P N : BHist) : BoundedLinearFunctionalUp
  deriving DecidableEq

def boundedLinearFunctionalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedLinearFunctionalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedLinearFunctionalEncodeBHist h

def boundedLinearFunctionalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedLinearFunctionalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedLinearFunctionalDecodeBHist tail)

private theorem BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedLinearFunctionalFields : BoundedLinearFunctionalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedLinearFunctionalUp.mk E L T K O H C P N => [E, L, T, K, O, H, C, P, N]

def boundedLinearFunctionalToEventFlow : BoundedLinearFunctionalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedLinearFunctionalFields x).map boundedLinearFunctionalEncodeBHist

private def boundedLinearFunctionalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedLinearFunctionalEventAt index rest

def boundedLinearFunctionalFromEventFlow :
    EventFlow → Option BoundedLinearFunctionalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BoundedLinearFunctionalUp.mk
        (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEventAt 0 ef))
        (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEventAt 1 ef))
        (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEventAt 2 ef))
        (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEventAt 3 ef))
        (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEventAt 4 ef))
        (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEventAt 5 ef))
        (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEventAt 6 ef))
        (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEventAt 7 ef))
        (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEventAt 8 ef)))

private theorem BoundedLinearFunctionalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedLinearFunctionalUp,
      boundedLinearFunctionalFromEventFlow (boundedLinearFunctionalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E L T K O H C P N =>
      change
        some
          (BoundedLinearFunctionalUp.mk
            (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist E))
            (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist L))
            (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist T))
            (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist K))
            (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist O))
            (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist H))
            (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist C))
            (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist P))
            (boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist N))) =
          some (BoundedLinearFunctionalUp.mk E L T K O H C P N)
      rw [BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode E,
        BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode L,
        BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode T,
        BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode K,
        BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode O,
        BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode H,
        BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode C,
        BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode P,
        BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode N]

private theorem boundedLinearFunctionalToEventFlow_injective
    {x y : BoundedLinearFunctionalUp} :
    boundedLinearFunctionalToEventFlow x = boundedLinearFunctionalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedLinearFunctionalFromEventFlow (boundedLinearFunctionalToEventFlow x) =
        boundedLinearFunctionalFromEventFlow (boundedLinearFunctionalToEventFlow y) :=
    congrArg boundedLinearFunctionalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedLinearFunctionalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedLinearFunctionalTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedLinearFunctionalTasteGate_single_carrier_alignment_fields :
    ∀ x y : BoundedLinearFunctionalUp,
      boundedLinearFunctionalFields x = boundedLinearFunctionalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E1 L1 T1 K1 O1 H1 C1 P1 N1 =>
      cases y with
      | mk E2 L2 T2 K2 O2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance boundedLinearFunctionalBHistCarrier :
    BHistCarrier BoundedLinearFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedLinearFunctionalToEventFlow
  fromEventFlow := boundedLinearFunctionalFromEventFlow

instance boundedLinearFunctionalChapterTasteGate :
    ChapterTasteGate BoundedLinearFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedLinearFunctionalFromEventFlow (boundedLinearFunctionalToEventFlow x) = some x
    exact BoundedLinearFunctionalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedLinearFunctionalToEventFlow_injective heq)

instance boundedLinearFunctionalFieldFaithful :
    FieldFaithful BoundedLinearFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedLinearFunctionalFields
  field_faithful := BoundedLinearFunctionalTasteGate_single_carrier_alignment_fields

instance boundedLinearFunctionalNontrivial :
    Nontrivial BoundedLinearFunctionalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedLinearFunctionalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedLinearFunctionalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedLinearFunctionalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedLinearFunctionalChapterTasteGate

theorem BoundedLinearFunctionalTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedLinearFunctionalDecodeBHist (boundedLinearFunctionalEncodeBHist h) = h) ∧
      (∀ x : BoundedLinearFunctionalUp,
        boundedLinearFunctionalFromEventFlow (boundedLinearFunctionalToEventFlow x) = some x) ∧
        (∀ x y : BoundedLinearFunctionalUp,
          boundedLinearFunctionalToEventFlow x = boundedLinearFunctionalToEventFlow y -> x = y) ∧
          boundedLinearFunctionalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨BoundedLinearFunctionalTasteGate_single_carrier_alignment_decode,
      BoundedLinearFunctionalTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact boundedLinearFunctionalToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BoundedLinearFunctionalUp
