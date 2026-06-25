import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HahnMazurkiewiczBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HahnMazurkiewiczBoundaryUp : Type where
  | mk (K M C P B E T R N : BHist) : HahnMazurkiewiczBoundaryUp
  deriving DecidableEq

def hahnMazurkiewiczBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hahnMazurkiewiczBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hahnMazurkiewiczBoundaryEncodeBHist h

def hahnMazurkiewiczBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hahnMazurkiewiczBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hahnMazurkiewiczBoundaryDecodeBHist tail)

private theorem HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hahnMazurkiewiczBoundaryDecodeBHist
          (hahnMazurkiewiczBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hahnMazurkiewiczBoundaryFields : HahnMazurkiewiczBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HahnMazurkiewiczBoundaryUp.mk K M C P B E T R N => [K, M, C, P, B, E, T, R, N]

def hahnMazurkiewiczBoundaryToEventFlow : HahnMazurkiewiczBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hahnMazurkiewiczBoundaryFields x).map hahnMazurkiewiczBoundaryEncodeBHist

private def hahnMazurkiewiczBoundaryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hahnMazurkiewiczBoundaryEventAt index rest

def hahnMazurkiewiczBoundaryFromEventFlow (ef : EventFlow) :
    Option HahnMazurkiewiczBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HahnMazurkiewiczBoundaryUp.mk
      (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEventAt 0 ef))
      (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEventAt 1 ef))
      (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEventAt 2 ef))
      (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEventAt 3 ef))
      (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEventAt 4 ef))
      (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEventAt 5 ef))
      (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEventAt 6 ef))
      (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEventAt 7 ef))
      (hahnMazurkiewiczBoundaryDecodeBHist (hahnMazurkiewiczBoundaryEventAt 8 ef)))

private theorem HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : HahnMazurkiewiczBoundaryUp) :
    hahnMazurkiewiczBoundaryFromEventFlow (hahnMazurkiewiczBoundaryToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K M C P B E T R N =>
      change
        some
          (HahnMazurkiewiczBoundaryUp.mk
            (hahnMazurkiewiczBoundaryDecodeBHist
              (hahnMazurkiewiczBoundaryEncodeBHist K))
            (hahnMazurkiewiczBoundaryDecodeBHist
              (hahnMazurkiewiczBoundaryEncodeBHist M))
            (hahnMazurkiewiczBoundaryDecodeBHist
              (hahnMazurkiewiczBoundaryEncodeBHist C))
            (hahnMazurkiewiczBoundaryDecodeBHist
              (hahnMazurkiewiczBoundaryEncodeBHist P))
            (hahnMazurkiewiczBoundaryDecodeBHist
              (hahnMazurkiewiczBoundaryEncodeBHist B))
            (hahnMazurkiewiczBoundaryDecodeBHist
              (hahnMazurkiewiczBoundaryEncodeBHist E))
            (hahnMazurkiewiczBoundaryDecodeBHist
              (hahnMazurkiewiczBoundaryEncodeBHist T))
            (hahnMazurkiewiczBoundaryDecodeBHist
              (hahnMazurkiewiczBoundaryEncodeBHist R))
            (hahnMazurkiewiczBoundaryDecodeBHist
              (hahnMazurkiewiczBoundaryEncodeBHist N))) =
          some (HahnMazurkiewiczBoundaryUp.mk K M C P B E T R N)
      rw [HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode K,
        HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode M,
        HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode B,
        HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode E,
        HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode T,
        HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode R,
        HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode N]

private theorem HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_injective
    {x y : HahnMazurkiewiczBoundaryUp} :
    hahnMazurkiewiczBoundaryToEventFlow x = hahnMazurkiewiczBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hahnMazurkiewiczBoundaryFromEventFlow (hahnMazurkiewiczBoundaryToEventFlow x) =
        hahnMazurkiewiczBoundaryFromEventFlow (hahnMazurkiewiczBoundaryToEventFlow y) :=
    congrArg hahnMazurkiewiczBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance hahnMazurkiewiczBoundaryBHistCarrier :
    BHistCarrier HahnMazurkiewiczBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hahnMazurkiewiczBoundaryToEventFlow
  fromEventFlow := hahnMazurkiewiczBoundaryFromEventFlow

instance hahnMazurkiewiczBoundaryChapterTasteGate :
    ChapterTasteGate HahnMazurkiewiczBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hahnMazurkiewiczBoundaryFromEventFlow
        (hahnMazurkiewiczBoundaryToEventFlow x) =
      some x
    exact HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_injective heq)

theorem HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, hahnMazurkiewiczBoundaryDecodeBHist
      (hahnMazurkiewiczBoundaryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HahnMazurkiewiczBoundaryUp) ∧
        Nonempty (ChapterTasteGate HahnMazurkiewiczBoundaryUp) ∧
          hahnMazurkiewiczBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HahnMazurkiewiczBoundaryTasteGate_single_carrier_alignment_decode_encode,
      ⟨hahnMazurkiewiczBoundaryBHistCarrier⟩,
      ⟨hahnMazurkiewiczBoundaryChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.HahnMazurkiewiczBoundaryUp
