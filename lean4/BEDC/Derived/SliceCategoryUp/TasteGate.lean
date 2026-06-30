import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SliceCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SliceCategoryUp : Type where
  | mk (B X A F H C P N : BHist) : SliceCategoryUp
  deriving DecidableEq

def sliceCategoryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sliceCategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sliceCategoryEncodeBHist h

def sliceCategoryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sliceCategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sliceCategoryDecodeBHist tail)

private theorem SliceCategoryTasteGate_single_carrier_alignment_decode :
    forall h : BHist, sliceCategoryDecodeBHist (sliceCategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sliceCategoryFields : SliceCategoryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SliceCategoryUp.mk B X A F H C P N => [B, X, A, F, H, C, P, N]

def sliceCategoryToEventFlow : SliceCategoryUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sliceCategoryFields x).map sliceCategoryEncodeBHist

private def sliceCategoryEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sliceCategoryEventAtDefault index rest

def sliceCategoryFromEventFlow (ef : EventFlow) : Option SliceCategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SliceCategoryUp.mk
      (sliceCategoryDecodeBHist (sliceCategoryEventAtDefault 0 ef))
      (sliceCategoryDecodeBHist (sliceCategoryEventAtDefault 1 ef))
      (sliceCategoryDecodeBHist (sliceCategoryEventAtDefault 2 ef))
      (sliceCategoryDecodeBHist (sliceCategoryEventAtDefault 3 ef))
      (sliceCategoryDecodeBHist (sliceCategoryEventAtDefault 4 ef))
      (sliceCategoryDecodeBHist (sliceCategoryEventAtDefault 5 ef))
      (sliceCategoryDecodeBHist (sliceCategoryEventAtDefault 6 ef))
      (sliceCategoryDecodeBHist (sliceCategoryEventAtDefault 7 ef)))

private theorem SliceCategoryTasteGate_single_carrier_alignment_round_trip :
    forall x : SliceCategoryUp,
      sliceCategoryFromEventFlow (sliceCategoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B X A F H C P N =>
      change
        some
          (SliceCategoryUp.mk
            (sliceCategoryDecodeBHist (sliceCategoryEncodeBHist B))
            (sliceCategoryDecodeBHist (sliceCategoryEncodeBHist X))
            (sliceCategoryDecodeBHist (sliceCategoryEncodeBHist A))
            (sliceCategoryDecodeBHist (sliceCategoryEncodeBHist F))
            (sliceCategoryDecodeBHist (sliceCategoryEncodeBHist H))
            (sliceCategoryDecodeBHist (sliceCategoryEncodeBHist C))
            (sliceCategoryDecodeBHist (sliceCategoryEncodeBHist P))
            (sliceCategoryDecodeBHist (sliceCategoryEncodeBHist N))) =
          some (SliceCategoryUp.mk B X A F H C P N)
      rw [SliceCategoryTasteGate_single_carrier_alignment_decode B,
        SliceCategoryTasteGate_single_carrier_alignment_decode X,
        SliceCategoryTasteGate_single_carrier_alignment_decode A,
        SliceCategoryTasteGate_single_carrier_alignment_decode F,
        SliceCategoryTasteGate_single_carrier_alignment_decode H,
        SliceCategoryTasteGate_single_carrier_alignment_decode C,
        SliceCategoryTasteGate_single_carrier_alignment_decode P,
        SliceCategoryTasteGate_single_carrier_alignment_decode N]

private theorem sliceCategoryToEventFlow_injective {x y : SliceCategoryUp} :
    sliceCategoryToEventFlow x = sliceCategoryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sliceCategoryFromEventFlow (sliceCategoryToEventFlow x) =
        sliceCategoryFromEventFlow (sliceCategoryToEventFlow y) :=
    congrArg sliceCategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SliceCategoryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SliceCategoryTasteGate_single_carrier_alignment_round_trip y)))

private theorem SliceCategoryTasteGate_single_carrier_alignment_fields :
    forall x y : SliceCategoryUp, sliceCategoryFields x = sliceCategoryFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance sliceCategoryBHistCarrier : BHistCarrier SliceCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sliceCategoryToEventFlow
  fromEventFlow := sliceCategoryFromEventFlow

instance sliceCategoryChapterTasteGate : ChapterTasteGate SliceCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sliceCategoryFromEventFlow (sliceCategoryToEventFlow x) = some x
    exact SliceCategoryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sliceCategoryToEventFlow_injective heq)

instance sliceCategoryFieldFaithful : FieldFaithful SliceCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sliceCategoryFields
  field_faithful := SliceCategoryTasteGate_single_carrier_alignment_fields

instance sliceCategoryNontrivial : Nontrivial SliceCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SliceCategoryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SliceCategoryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SliceCategoryTasteGate_single_carrier_alignment :
    (forall h : BHist, sliceCategoryDecodeBHist (sliceCategoryEncodeBHist h) = h) ∧
      (forall x : SliceCategoryUp,
        sliceCategoryFromEventFlow (sliceCategoryToEventFlow x) = some x) ∧
        (forall x y : SliceCategoryUp,
          sliceCategoryToEventFlow x = sliceCategoryToEventFlow y -> x = y) ∧
          sliceCategoryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SliceCategoryTasteGate_single_carrier_alignment_decode,
      SliceCategoryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => sliceCategoryToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SliceCategoryUp
