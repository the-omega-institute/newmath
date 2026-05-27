import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubtypeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubtypeUp : Type where
  | mk (carrier predicate : BHist) : SubtypeUp
  deriving DecidableEq

def subtypeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subtypeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subtypeEncodeBHist h

def subtypeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subtypeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subtypeDecodeBHist tail)

private theorem SubtypeTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, subtypeDecodeBHist (subtypeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def subtypeToEventFlow : SubtypeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubtypeUp.mk carrier predicate =>
      [[BMark.b0, BMark.b1, BMark.b1, BMark.b0],
        subtypeEncodeBHist carrier,
        subtypeEncodeBHist predicate]

def subtypeFromEventFlow : EventFlow -> Option SubtypeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restCarrier =>
      match restCarrier with
      | [] => none
      | carrier :: restPredicate =>
          match restPredicate with
          | [] => none
          | predicate :: rest =>
              match rest with
              | [] =>
                  some
                    (SubtypeUp.mk
                      (subtypeDecodeBHist carrier)
                      (subtypeDecodeBHist predicate))
              | _ :: _ => none

private theorem SubtypeTasteGate_single_carrier_alignment_round_trip :
    forall x : SubtypeUp, subtypeFromEventFlow (subtypeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carrier predicate =>
      change
        some
          (SubtypeUp.mk
            (subtypeDecodeBHist (subtypeEncodeBHist carrier))
            (subtypeDecodeBHist (subtypeEncodeBHist predicate))) =
          some (SubtypeUp.mk carrier predicate)
      rw [SubtypeTasteGate_single_carrier_alignment_decode_encode carrier,
        SubtypeTasteGate_single_carrier_alignment_decode_encode predicate]

private theorem SubtypeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SubtypeUp} :
    subtypeToEventFlow x = subtypeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subtypeFromEventFlow (subtypeToEventFlow x) =
        subtypeFromEventFlow (subtypeToEventFlow y) :=
    congrArg subtypeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SubtypeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SubtypeTasteGate_single_carrier_alignment_round_trip y)))

instance subtypeBHistCarrier : BHistCarrier SubtypeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subtypeToEventFlow
  fromEventFlow := subtypeFromEventFlow

instance subtypeChapterTasteGate : ChapterTasteGate SubtypeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subtypeFromEventFlow (subtypeToEventFlow x) = some x
    exact SubtypeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SubtypeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SubtypeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subtypeChapterTasteGate

theorem SubtypeTasteGate_single_carrier_alignment :
    (forall h : BHist, subtypeDecodeBHist (subtypeEncodeBHist h) = h) ∧
      (forall x : SubtypeUp, subtypeFromEventFlow (subtypeToEventFlow x) = some x) ∧
        (forall x y : SubtypeUp, subtypeToEventFlow x = subtypeToEventFlow y -> x = y) ∧
          subtypeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SubtypeTasteGate_single_carrier_alignment_decode_encode,
      SubtypeTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => SubtypeTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.SubtypeUp
