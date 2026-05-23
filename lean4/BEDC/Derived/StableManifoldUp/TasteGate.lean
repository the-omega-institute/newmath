import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StableManifoldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StableManifoldUp : Type where
  | mk (E D O M L T H C P N : BHist) : StableManifoldUp
  deriving DecidableEq

def stableManifoldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stableManifoldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stableManifoldEncodeBHist h

def stableManifoldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stableManifoldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stableManifoldDecodeBHist tail)

private theorem StableManifoldTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, stableManifoldDecodeBHist (stableManifoldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stableManifoldFields : StableManifoldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StableManifoldUp.mk E D O M L T H C P N => [E, D, O, M, L, T, H, C, P, N]

def stableManifoldToEventFlow : StableManifoldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (stableManifoldFields x).map stableManifoldEncodeBHist

private def stableManifoldRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => stableManifoldRawAt index rest

def stableManifoldFromEventFlow (flow : EventFlow) : Option StableManifoldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StableManifoldUp.mk
      (stableManifoldDecodeBHist (stableManifoldRawAt 0 flow))
      (stableManifoldDecodeBHist (stableManifoldRawAt 1 flow))
      (stableManifoldDecodeBHist (stableManifoldRawAt 2 flow))
      (stableManifoldDecodeBHist (stableManifoldRawAt 3 flow))
      (stableManifoldDecodeBHist (stableManifoldRawAt 4 flow))
      (stableManifoldDecodeBHist (stableManifoldRawAt 5 flow))
      (stableManifoldDecodeBHist (stableManifoldRawAt 6 flow))
      (stableManifoldDecodeBHist (stableManifoldRawAt 7 flow))
      (stableManifoldDecodeBHist (stableManifoldRawAt 8 flow))
      (stableManifoldDecodeBHist (stableManifoldRawAt 9 flow)))

private theorem stableManifold_round_trip :
    ∀ x : StableManifoldUp,
      stableManifoldFromEventFlow (stableManifoldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E D O M L T H C P N =>
      change
        some
          (StableManifoldUp.mk
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist E))
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist D))
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist O))
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist M))
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist L))
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist T))
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist H))
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist C))
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist P))
            (stableManifoldDecodeBHist (stableManifoldEncodeBHist N))) =
          some (StableManifoldUp.mk E D O M L T H C P N)
      rw [StableManifoldTasteGate_single_carrier_alignment_decode E,
        StableManifoldTasteGate_single_carrier_alignment_decode D,
        StableManifoldTasteGate_single_carrier_alignment_decode O,
        StableManifoldTasteGate_single_carrier_alignment_decode M,
        StableManifoldTasteGate_single_carrier_alignment_decode L,
        StableManifoldTasteGate_single_carrier_alignment_decode T,
        StableManifoldTasteGate_single_carrier_alignment_decode H,
        StableManifoldTasteGate_single_carrier_alignment_decode C,
        StableManifoldTasteGate_single_carrier_alignment_decode P,
        StableManifoldTasteGate_single_carrier_alignment_decode N]

private theorem stableManifoldToEventFlow_injective
    {x y : StableManifoldUp} :
    stableManifoldToEventFlow x = stableManifoldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stableManifoldFromEventFlow (stableManifoldToEventFlow x) =
        stableManifoldFromEventFlow (stableManifoldToEventFlow y) :=
    congrArg stableManifoldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stableManifold_round_trip x).symm
      (Eq.trans hread (stableManifold_round_trip y)))

private theorem StableManifoldTasteGate_single_carrier_alignment_fields :
    ∀ x y : StableManifoldUp, stableManifoldFields x = stableManifoldFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E1 D1 O1 M1 L1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk E2 D2 O2 M2 L2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance stableManifoldBHistCarrier : BHistCarrier StableManifoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stableManifoldToEventFlow
  fromEventFlow := stableManifoldFromEventFlow

instance stableManifoldChapterTasteGate :
    ChapterTasteGate StableManifoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change stableManifoldFromEventFlow (stableManifoldToEventFlow x) = some x
    exact stableManifold_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stableManifoldToEventFlow_injective heq)

def taste_gate : ChapterTasteGate StableManifoldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stableManifoldChapterTasteGate

instance stableManifoldFieldFaithful : FieldFaithful StableManifoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := stableManifoldFields
  field_faithful := StableManifoldTasteGate_single_carrier_alignment_fields

instance stableManifoldNontrivial : Nontrivial StableManifoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StableManifoldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StableManifoldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem StableManifoldTasteGate_single_carrier_alignment :
    (∀ h : BHist, stableManifoldDecodeBHist (stableManifoldEncodeBHist h) = h) ∧
      (∀ x : StableManifoldUp,
        stableManifoldFromEventFlow (stableManifoldToEventFlow x) = some x) ∧
      (∀ x y : StableManifoldUp,
        stableManifoldToEventFlow x = stableManifoldToEventFlow y → x = y) ∧
      stableManifoldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨StableManifoldTasteGate_single_carrier_alignment_decode,
      stableManifold_round_trip,
      by
        intro x y heq
        exact stableManifoldToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.StableManifoldUp
