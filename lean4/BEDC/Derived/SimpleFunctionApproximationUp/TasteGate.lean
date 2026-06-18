import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SimpleFunctionApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SimpleFunctionApproximationUp : Type where
  | mk (M F R E T O H C P N : BHist) : SimpleFunctionApproximationUp
  deriving DecidableEq

def simpleFunctionApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: simpleFunctionApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: simpleFunctionApproximationEncodeBHist h

def simpleFunctionApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (simpleFunctionApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (simpleFunctionApproximationDecodeBHist tail)

private theorem SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      simpleFunctionApproximationDecodeBHist
        (simpleFunctionApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def simpleFunctionApproximationFields :
    SimpleFunctionApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SimpleFunctionApproximationUp.mk M F R E T O H C P N => [M, F, R, E, T, O, H, C, P, N]

private def simpleFunctionApproximationToEventFlow :
    SimpleFunctionApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (simpleFunctionApproximationFields x).map simpleFunctionApproximationEncodeBHist

private def SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt index rest

private def simpleFunctionApproximationFromEventFlow
    (ef : EventFlow) : Option SimpleFunctionApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SimpleFunctionApproximationUp.mk
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 0 ef))
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 1 ef))
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 2 ef))
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 3 ef))
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 4 ef))
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 5 ef))
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 6 ef))
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 7 ef))
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 8 ef))
      (simpleFunctionApproximationDecodeBHist
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem SimpleFunctionApproximationTasteGate_single_carrier_alignment_round_trip
    (x : SimpleFunctionApproximationUp) :
    simpleFunctionApproximationFromEventFlow
      (simpleFunctionApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M F R E T O H C P N =>
      change
        some
          (SimpleFunctionApproximationUp.mk
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist M))
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist F))
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist R))
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist E))
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist T))
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist O))
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist H))
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist C))
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist P))
            (simpleFunctionApproximationDecodeBHist
              (simpleFunctionApproximationEncodeBHist N))) =
          some (SimpleFunctionApproximationUp.mk M F R E T O H C P N)
      rw [SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode M,
        SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode F,
        SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode R,
        SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode E,
        SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode T,
        SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode O,
        SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode H,
        SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode C,
        SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode P,
        SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode N]

private theorem SimpleFunctionApproximationTasteGate_single_carrier_alignment_injective
    {x y : SimpleFunctionApproximationUp} :
    simpleFunctionApproximationToEventFlow x =
      simpleFunctionApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      simpleFunctionApproximationFromEventFlow
          (simpleFunctionApproximationToEventFlow x) =
        simpleFunctionApproximationFromEventFlow
          (simpleFunctionApproximationToEventFlow y) :=
    congrArg simpleFunctionApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SimpleFunctionApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SimpleFunctionApproximationTasteGate_single_carrier_alignment_round_trip y)))

instance simpleFunctionApproximationBHistCarrier :
    BHistCarrier SimpleFunctionApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := simpleFunctionApproximationToEventFlow
  fromEventFlow := simpleFunctionApproximationFromEventFlow

instance simpleFunctionApproximationChapterTasteGate :
    ChapterTasteGate SimpleFunctionApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      simpleFunctionApproximationFromEventFlow
          (simpleFunctionApproximationToEventFlow x) =
        some x
    exact SimpleFunctionApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SimpleFunctionApproximationTasteGate_single_carrier_alignment_injective heq)

theorem SimpleFunctionApproximationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      simpleFunctionApproximationDecodeBHist
        (simpleFunctionApproximationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SimpleFunctionApproximationUp) ∧
        Nonempty (ChapterTasteGate SimpleFunctionApproximationUp) ∧
          simpleFunctionApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SimpleFunctionApproximationTasteGate_single_carrier_alignment_decode,
      ⟨⟨simpleFunctionApproximationBHistCarrier⟩,
        ⟨⟨simpleFunctionApproximationChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.SimpleFunctionApproximationUp
