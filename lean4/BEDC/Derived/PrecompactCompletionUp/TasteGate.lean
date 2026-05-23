import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrecompactCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrecompactCompletionUp : Type where
  | mk (X N F E C S H R Q L : BHist) : PrecompactCompletionUp
  deriving DecidableEq

def precompactCompletionEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: precompactCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: precompactCompletionEncodeBHist h

def precompactCompletionDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (precompactCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (precompactCompletionDecodeBHist tail)

private theorem PrecompactCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      precompactCompletionDecodeBHist (precompactCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def precompactCompletionFields : PrecompactCompletionUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | PrecompactCompletionUp.mk X N F E C S H R Q L => [X, N, F, E, C, S, H, R, Q, L]

def precompactCompletionToEventFlow : PrecompactCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => List.map precompactCompletionEncodeBHist (precompactCompletionFields x)

private def precompactCompletionEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => precompactCompletionEventAt index rest

def precompactCompletionFromEventFlow : EventFlow → Option PrecompactCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (PrecompactCompletionUp.mk
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 0 ef))
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 1 ef))
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 2 ef))
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 3 ef))
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 4 ef))
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 5 ef))
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 6 ef))
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 7 ef))
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 8 ef))
        (precompactCompletionDecodeBHist (precompactCompletionEventAt 9 ef)))

private theorem PrecompactCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PrecompactCompletionUp,
      precompactCompletionFromEventFlow (precompactCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X N F E C S H R Q L =>
      change
        some
            (PrecompactCompletionUp.mk
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist X))
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist N))
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist F))
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist E))
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist C))
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist S))
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist H))
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist R))
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist Q))
              (precompactCompletionDecodeBHist (precompactCompletionEncodeBHist L))) =
          some (PrecompactCompletionUp.mk X N F E C S H R Q L)
      rw [PrecompactCompletionTasteGate_single_carrier_alignment_decode X,
        PrecompactCompletionTasteGate_single_carrier_alignment_decode N,
        PrecompactCompletionTasteGate_single_carrier_alignment_decode F,
        PrecompactCompletionTasteGate_single_carrier_alignment_decode E,
        PrecompactCompletionTasteGate_single_carrier_alignment_decode C,
        PrecompactCompletionTasteGate_single_carrier_alignment_decode S,
        PrecompactCompletionTasteGate_single_carrier_alignment_decode H,
        PrecompactCompletionTasteGate_single_carrier_alignment_decode R,
        PrecompactCompletionTasteGate_single_carrier_alignment_decode Q,
        PrecompactCompletionTasteGate_single_carrier_alignment_decode L]

private theorem precompactCompletionToEventFlow_injective {x y : PrecompactCompletionUp} :
    precompactCompletionToEventFlow x = precompactCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x = precompactCompletionFromEventFlow (precompactCompletionToEventFlow x) :=
        (PrecompactCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      _ = precompactCompletionFromEventFlow (precompactCompletionToEventFlow y) :=
        congrArg precompactCompletionFromEventFlow hxy
      _ = some y := PrecompactCompletionTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj hsome

instance precompactCompletionBHistCarrier : BHistCarrier PrecompactCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := precompactCompletionToEventFlow
  fromEventFlow := precompactCompletionFromEventFlow

instance precompactCompletionChapterTasteGate : ChapterTasteGate PrecompactCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change precompactCompletionFromEventFlow (precompactCompletionToEventFlow x) = some x
    exact PrecompactCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (precompactCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PrecompactCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  precompactCompletionChapterTasteGate

theorem PrecompactCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, precompactCompletionDecodeBHist (precompactCompletionEncodeBHist h) = h) ∧
      (∀ x : PrecompactCompletionUp,
        precompactCompletionFromEventFlow (precompactCompletionToEventFlow x) = some x) ∧
        (∀ x y : PrecompactCompletionUp,
          precompactCompletionToEventFlow x = precompactCompletionToEventFlow y → x = y) ∧
          precompactCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PrecompactCompletionTasteGate_single_carrier_alignment_decode,
      PrecompactCompletionTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact precompactCompletionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.PrecompactCompletionUp
