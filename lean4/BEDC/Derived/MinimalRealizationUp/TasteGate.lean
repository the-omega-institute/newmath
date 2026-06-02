import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinimalRealizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinimalRealizationUp : Type where
  | mk (X U Y A B C D Q O Go Gr n m I L T P N : BHist) : MinimalRealizationUp
  deriving DecidableEq

def minimalRealizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minimalRealizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minimalRealizationEncodeBHist h

def minimalRealizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minimalRealizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minimalRealizationDecodeBHist tail)

private theorem MinimalRealizationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, minimalRealizationDecodeBHist (minimalRealizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def minimalRealizationFields : MinimalRealizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MinimalRealizationUp.mk X U Y A B C D Q O Go Gr n m I L T P N =>
      [X, U, Y, A, B, C, D, Q, O, Go, Gr, n, m, I, L, T, P, N]

def minimalRealizationToEventFlow : MinimalRealizationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (minimalRealizationFields x).map minimalRealizationEncodeBHist

private def minimalRealizationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => minimalRealizationEventAtDefault index rest

def minimalRealizationFromEventFlow : EventFlow → Option MinimalRealizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MinimalRealizationUp.mk
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 0 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 1 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 2 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 3 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 4 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 5 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 6 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 7 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 8 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 9 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 10 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 11 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 12 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 13 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 14 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 15 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 16 ef))
        (minimalRealizationDecodeBHist (minimalRealizationEventAtDefault 17 ef)))

private theorem MinimalRealizationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MinimalRealizationUp,
      minimalRealizationFromEventFlow (minimalRealizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X U Y A B C D Q O Go Gr n m I L T P N =>
      change
        some
          (MinimalRealizationUp.mk
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist X))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist U))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist Y))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist A))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist B))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist C))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist D))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist Q))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist O))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist Go))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist Gr))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist n))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist m))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist I))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist L))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist T))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist P))
            (minimalRealizationDecodeBHist (minimalRealizationEncodeBHist N))) =
          some (MinimalRealizationUp.mk X U Y A B C D Q O Go Gr n m I L T P N)
      rw [MinimalRealizationTasteGate_single_carrier_alignment_decode X,
        MinimalRealizationTasteGate_single_carrier_alignment_decode U,
        MinimalRealizationTasteGate_single_carrier_alignment_decode Y,
        MinimalRealizationTasteGate_single_carrier_alignment_decode A,
        MinimalRealizationTasteGate_single_carrier_alignment_decode B,
        MinimalRealizationTasteGate_single_carrier_alignment_decode C,
        MinimalRealizationTasteGate_single_carrier_alignment_decode D,
        MinimalRealizationTasteGate_single_carrier_alignment_decode Q,
        MinimalRealizationTasteGate_single_carrier_alignment_decode O,
        MinimalRealizationTasteGate_single_carrier_alignment_decode Go,
        MinimalRealizationTasteGate_single_carrier_alignment_decode Gr,
        MinimalRealizationTasteGate_single_carrier_alignment_decode n,
        MinimalRealizationTasteGate_single_carrier_alignment_decode m,
        MinimalRealizationTasteGate_single_carrier_alignment_decode I,
        MinimalRealizationTasteGate_single_carrier_alignment_decode L,
        MinimalRealizationTasteGate_single_carrier_alignment_decode T,
        MinimalRealizationTasteGate_single_carrier_alignment_decode P,
        MinimalRealizationTasteGate_single_carrier_alignment_decode N]

private theorem MinimalRealizationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MinimalRealizationUp} :
    minimalRealizationToEventFlow x = minimalRealizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minimalRealizationFromEventFlow (minimalRealizationToEventFlow x) =
        minimalRealizationFromEventFlow (minimalRealizationToEventFlow y) :=
    congrArg minimalRealizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MinimalRealizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MinimalRealizationTasteGate_single_carrier_alignment_round_trip y)))

instance minimalRealizationBHistCarrier : BHistCarrier MinimalRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minimalRealizationToEventFlow
  fromEventFlow := minimalRealizationFromEventFlow

instance minimalRealizationChapterTasteGate : ChapterTasteGate MinimalRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change minimalRealizationFromEventFlow (minimalRealizationToEventFlow x) = some x
    exact MinimalRealizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MinimalRealizationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MinimalRealizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  minimalRealizationChapterTasteGate

theorem MinimalRealizationTasteGate_single_carrier_alignment :
    (∀ h : BHist, minimalRealizationDecodeBHist (minimalRealizationEncodeBHist h) = h) ∧
      (∀ x : MinimalRealizationUp,
        minimalRealizationFromEventFlow (minimalRealizationToEventFlow x) = some x) ∧
        (∀ x y : MinimalRealizationUp,
          minimalRealizationToEventFlow x = minimalRealizationToEventFlow y → x = y) ∧
          minimalRealizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MinimalRealizationTasteGate_single_carrier_alignment_decode,
      MinimalRealizationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MinimalRealizationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MinimalRealizationUp
