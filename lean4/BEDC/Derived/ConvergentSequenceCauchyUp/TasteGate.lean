import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConvergentSequenceCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConvergentSequenceCauchyUp : Type where
  | mk : (L W D K R E H C P N : BHist) -> ConvergentSequenceCauchyUp

def convergentSequenceCauchyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: convergentSequenceCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: convergentSequenceCauchyEncodeBHist h

def convergentSequenceCauchyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (convergentSequenceCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (convergentSequenceCauchyDecodeBHist tail)

theorem ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def convergentSequenceCauchyFields : ConvergentSequenceCauchyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConvergentSequenceCauchyUp.mk L W D K R E H C P N => [L, W, D, K, R, E, H, C, P, N]

def convergentSequenceCauchyToEventFlow : ConvergentSequenceCauchyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (convergentSequenceCauchyFields x).map convergentSequenceCauchyEncodeBHist

def convergentSequenceCauchyEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => convergentSequenceCauchyEventAtDefault index rest

def convergentSequenceCauchyFromEventFlow : EventFlow -> Option ConvergentSequenceCauchyUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ConvergentSequenceCauchyUp.mk
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 0 ef))
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 1 ef))
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 2 ef))
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 3 ef))
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 4 ef))
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 5 ef))
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 6 ef))
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 7 ef))
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 8 ef))
          (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEventAtDefault 9 ef)))

theorem ConvergentSequenceCauchyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConvergentSequenceCauchyUp,
      convergentSequenceCauchyFromEventFlow (convergentSequenceCauchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L W D K R E H C P N =>
      change
        some
          (ConvergentSequenceCauchyUp.mk
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist L))
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist W))
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist D))
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist K))
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist R))
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist E))
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist H))
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist C))
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist P))
            (convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist N))) =
          some (ConvergentSequenceCauchyUp.mk L W D K R E H C P N)
      rw [ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode L,
        ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode W,
        ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode D,
        ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode K,
        ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode R,
        ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode E,
        ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode H,
        ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode C,
        ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode P,
        ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode N]

theorem ConvergentSequenceCauchyTasteGate_single_carrier_alignment_injective
    {x y : ConvergentSequenceCauchyUp} :
    convergentSequenceCauchyToEventFlow x = convergentSequenceCauchyToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      convergentSequenceCauchyFromEventFlow (convergentSequenceCauchyToEventFlow x) =
        convergentSequenceCauchyFromEventFlow (convergentSequenceCauchyToEventFlow y) :=
    congrArg convergentSequenceCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConvergentSequenceCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConvergentSequenceCauchyTasteGate_single_carrier_alignment_round_trip y)))

instance convergentSequenceCauchyBHistCarrier : BHistCarrier ConvergentSequenceCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := convergentSequenceCauchyToEventFlow
  fromEventFlow := convergentSequenceCauchyFromEventFlow

instance convergentSequenceCauchyChapterTasteGate : ChapterTasteGate ConvergentSequenceCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => ConvergentSequenceCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConvergentSequenceCauchyTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate ConvergentSequenceCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  convergentSequenceCauchyChapterTasteGate

theorem ConvergentSequenceCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist, convergentSequenceCauchyDecodeBHist (convergentSequenceCauchyEncodeBHist h) = h) ∧
      (∀ x : ConvergentSequenceCauchyUp,
        convergentSequenceCauchyFromEventFlow (convergentSequenceCauchyToEventFlow x) = some x) ∧
        (∀ x y : ConvergentSequenceCauchyUp,
          convergentSequenceCauchyToEventFlow x = convergentSequenceCauchyToEventFlow y -> x = y) ∧
          convergentSequenceCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ConvergentSequenceCauchyTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ConvergentSequenceCauchyTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ConvergentSequenceCauchyTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ConvergentSequenceCauchyUp
