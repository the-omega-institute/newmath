import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RieszRepresentationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RieszRepresentationUp : Type where
  | mk
      (sourceRow functionalRow representingDatum scalarLedger branchBoundary : BHist) :
      RieszRepresentationUp
  deriving DecidableEq

def rieszRepresentationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rieszRepresentationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rieszRepresentationEncodeBHist h

def rieszRepresentationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rieszRepresentationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rieszRepresentationDecodeBHist tail)

private theorem RieszRepresentationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, rieszRepresentationDecodeBHist (rieszRepresentationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rieszRepresentationFields : RieszRepresentationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RieszRepresentationUp.mk sourceRow functionalRow representingDatum scalarLedger
      branchBoundary =>
      [sourceRow, functionalRow, representingDatum, scalarLedger, branchBoundary]

def rieszRepresentationToEventFlow : RieszRepresentationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rieszRepresentationFields x).map rieszRepresentationEncodeBHist

private def rieszRepresentationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rieszRepresentationEventAtDefault index rest

def rieszRepresentationFromEventFlow : EventFlow → Option RieszRepresentationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RieszRepresentationUp.mk
        (rieszRepresentationDecodeBHist (rieszRepresentationEventAtDefault 0 ef))
        (rieszRepresentationDecodeBHist (rieszRepresentationEventAtDefault 1 ef))
        (rieszRepresentationDecodeBHist (rieszRepresentationEventAtDefault 2 ef))
        (rieszRepresentationDecodeBHist (rieszRepresentationEventAtDefault 3 ef))
        (rieszRepresentationDecodeBHist (rieszRepresentationEventAtDefault 4 ef)))

private theorem RieszRepresentationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RieszRepresentationUp,
      rieszRepresentationFromEventFlow (rieszRepresentationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceRow functionalRow representingDatum scalarLedger branchBoundary =>
      change
        some
          (RieszRepresentationUp.mk
            (rieszRepresentationDecodeBHist (rieszRepresentationEncodeBHist sourceRow))
            (rieszRepresentationDecodeBHist (rieszRepresentationEncodeBHist functionalRow))
            (rieszRepresentationDecodeBHist (rieszRepresentationEncodeBHist representingDatum))
            (rieszRepresentationDecodeBHist (rieszRepresentationEncodeBHist scalarLedger))
            (rieszRepresentationDecodeBHist (rieszRepresentationEncodeBHist branchBoundary))) =
          some
            (RieszRepresentationUp.mk sourceRow functionalRow representingDatum scalarLedger
              branchBoundary)
      rw [RieszRepresentationTasteGate_single_carrier_alignment_decode sourceRow,
        RieszRepresentationTasteGate_single_carrier_alignment_decode functionalRow,
        RieszRepresentationTasteGate_single_carrier_alignment_decode representingDatum,
        RieszRepresentationTasteGate_single_carrier_alignment_decode scalarLedger,
        RieszRepresentationTasteGate_single_carrier_alignment_decode branchBoundary]

private theorem RieszRepresentationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RieszRepresentationUp} :
    rieszRepresentationToEventFlow x = rieszRepresentationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rieszRepresentationFromEventFlow (rieszRepresentationToEventFlow x) =
        rieszRepresentationFromEventFlow (rieszRepresentationToEventFlow y) :=
    congrArg rieszRepresentationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RieszRepresentationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RieszRepresentationTasteGate_single_carrier_alignment_round_trip y)))

instance rieszRepresentationBHistCarrier : BHistCarrier RieszRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rieszRepresentationToEventFlow
  fromEventFlow := rieszRepresentationFromEventFlow

instance rieszRepresentationChapterTasteGate : ChapterTasteGate RieszRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rieszRepresentationFromEventFlow (rieszRepresentationToEventFlow x) = some x
    exact RieszRepresentationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RieszRepresentationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RieszRepresentationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rieszRepresentationChapterTasteGate

theorem RieszRepresentationTasteGate_single_carrier_alignment :
    (∀ h : BHist, rieszRepresentationDecodeBHist (rieszRepresentationEncodeBHist h) = h) ∧
      (∀ x : RieszRepresentationUp,
        rieszRepresentationFromEventFlow (rieszRepresentationToEventFlow x) = some x) ∧
        (∀ x y : RieszRepresentationUp,
          rieszRepresentationToEventFlow x = rieszRepresentationToEventFlow y → x = y) ∧
          rieszRepresentationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RieszRepresentationTasteGate_single_carrier_alignment_decode,
      RieszRepresentationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RieszRepresentationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RieszRepresentationUp
