import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedSearchRefutationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedSearchRefutationUp : Type where
  | mk (A K F R G H C P N : BHist) : BoundedSearchRefutationUp
  deriving DecidableEq

def boundedSearchRefutationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedSearchRefutationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedSearchRefutationEncodeBHist h

def boundedSearchRefutationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedSearchRefutationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedSearchRefutationDecodeBHist tail)

private theorem BoundedSearchRefutationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedSearchRefutationFields : BoundedSearchRefutationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedSearchRefutationUp.mk A K F R G H C P N => [A, K, F, R, G, H, C, P, N]

def boundedSearchRefutationToEventFlow : BoundedSearchRefutationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedSearchRefutationFields x).map boundedSearchRefutationEncodeBHist

private def boundedSearchRefutationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedSearchRefutationEventAtDefault index rest

def boundedSearchRefutationFromEventFlow : EventFlow → Option BoundedSearchRefutationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BoundedSearchRefutationUp.mk
        (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEventAtDefault 0 ef))
        (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEventAtDefault 1 ef))
        (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEventAtDefault 2 ef))
        (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEventAtDefault 3 ef))
        (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEventAtDefault 4 ef))
        (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEventAtDefault 5 ef))
        (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEventAtDefault 6 ef))
        (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEventAtDefault 7 ef))
        (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEventAtDefault 8 ef)))

private theorem BoundedSearchRefutationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedSearchRefutationUp,
      boundedSearchRefutationFromEventFlow (boundedSearchRefutationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A K F R G H C P N =>
      change
        some
            (BoundedSearchRefutationUp.mk
              (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist A))
              (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist K))
              (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist F))
              (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist R))
              (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist G))
              (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist H))
              (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist C))
              (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist P))
              (boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist N))) =
          some (BoundedSearchRefutationUp.mk A K F R G H C P N)
      rw [BoundedSearchRefutationTasteGate_single_carrier_alignment_decode A,
        BoundedSearchRefutationTasteGate_single_carrier_alignment_decode K,
        BoundedSearchRefutationTasteGate_single_carrier_alignment_decode F,
        BoundedSearchRefutationTasteGate_single_carrier_alignment_decode R,
        BoundedSearchRefutationTasteGate_single_carrier_alignment_decode G,
        BoundedSearchRefutationTasteGate_single_carrier_alignment_decode H,
        BoundedSearchRefutationTasteGate_single_carrier_alignment_decode C,
        BoundedSearchRefutationTasteGate_single_carrier_alignment_decode P,
        BoundedSearchRefutationTasteGate_single_carrier_alignment_decode N]

theorem BoundedSearchRefutationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        boundedSearchRefutationDecodeBHist (boundedSearchRefutationEncodeBHist h) = h) ∧
      (∀ x : BoundedSearchRefutationUp,
        boundedSearchRefutationFromEventFlow (boundedSearchRefutationToEventFlow x) = some x) ∧
      (∀ x y : BoundedSearchRefutationUp,
        boundedSearchRefutationToEventFlow x = boundedSearchRefutationToEventFlow y → x = y) ∧
      boundedSearchRefutationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BoundedSearchRefutationTasteGate_single_carrier_alignment_decode
  · constructor
    · exact BoundedSearchRefutationTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        have hread :
            boundedSearchRefutationFromEventFlow (boundedSearchRefutationToEventFlow x) =
              boundedSearchRefutationFromEventFlow (boundedSearchRefutationToEventFlow y) :=
          congrArg boundedSearchRefutationFromEventFlow heq
        exact Option.some.inj
          (Eq.trans
            (BoundedSearchRefutationTasteGate_single_carrier_alignment_round_trip x).symm
            (Eq.trans hread
              (BoundedSearchRefutationTasteGate_single_carrier_alignment_round_trip y)))
      · rfl

instance boundedSearchRefutationBHistCarrier : BHistCarrier BoundedSearchRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedSearchRefutationToEventFlow
  fromEventFlow := boundedSearchRefutationFromEventFlow

instance boundedSearchRefutationChapterTasteGate :
    ChapterTasteGate BoundedSearchRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedSearchRefutationFromEventFlow (boundedSearchRefutationToEventFlow x) = some x
    exact BoundedSearchRefutationTasteGate_single_carrier_alignment.right.left x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedSearchRefutationTasteGate_single_carrier_alignment.right.right.left x y heq)

instance boundedSearchRefutationNontrivial : Nontrivial BoundedSearchRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedSearchRefutationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedSearchRefutationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedSearchRefutationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedSearchRefutationChapterTasteGate

end BEDC.Derived.BoundedSearchRefutationUp
