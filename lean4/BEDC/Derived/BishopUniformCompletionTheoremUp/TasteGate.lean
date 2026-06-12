import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopUniformCompletionTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopUniformCompletionTheoremUp : Type where
  | mk (X F S R E V H C P N : BHist) : BishopUniformCompletionTheoremUp
  deriving DecidableEq

def bishopUniformCompletionTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopUniformCompletionTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopUniformCompletionTheoremEncodeBHist h

def bishopUniformCompletionTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopUniformCompletionTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopUniformCompletionTheoremDecodeBHist tail)

private theorem BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopUniformCompletionTheoremDecodeBHist
          (bishopUniformCompletionTheoremEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopUniformCompletionTheoremFields :
    BishopUniformCompletionTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopUniformCompletionTheoremUp.mk X F S R E V H C P N =>
      [X, F, S, R, E, V, H, C, P, N]

def bishopUniformCompletionTheoremToEventFlow :
    BishopUniformCompletionTheoremUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopUniformCompletionTheoremFields x).map
      bishopUniformCompletionTheoremEncodeBHist

private def bishopUniformCompletionTheoremRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopUniformCompletionTheoremRawAt index rest

def bishopUniformCompletionTheoremFromEventFlow
    (flow : EventFlow) : Option BishopUniformCompletionTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopUniformCompletionTheoremUp.mk
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 0 flow))
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 1 flow))
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 2 flow))
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 3 flow))
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 4 flow))
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 5 flow))
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 6 flow))
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 7 flow))
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 8 flow))
      (bishopUniformCompletionTheoremDecodeBHist
        (bishopUniformCompletionTheoremRawAt 9 flow)))

private theorem BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopUniformCompletionTheoremUp,
      bishopUniformCompletionTheoremFromEventFlow
          (bishopUniformCompletionTheoremToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F S R E V H C P N =>
      change
        some
            (BishopUniformCompletionTheoremUp.mk
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist X))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist F))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist S))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist R))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist E))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist V))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist H))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist C))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist P))
              (bishopUniformCompletionTheoremDecodeBHist
                (bishopUniformCompletionTheoremEncodeBHist N))) =
          some (BishopUniformCompletionTheoremUp.mk X F S R E V H C P N)
      rw [BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode X,
        BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode F,
        BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode S,
        BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode R,
        BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode E,
        BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode V,
        BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode H,
        BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode C,
        BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode P,
        BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode N]

private theorem BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopUniformCompletionTheoremUp} :
    bishopUniformCompletionTheoremToEventFlow x =
        bishopUniformCompletionTheoremToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopUniformCompletionTheoremFromEventFlow
          (bishopUniformCompletionTheoremToEventFlow x) =
        bishopUniformCompletionTheoremFromEventFlow
          (bishopUniformCompletionTheoremToEventFlow y) :=
    congrArg bishopUniformCompletionTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance bishopUniformCompletionTheoremBHistCarrier :
    BHistCarrier BishopUniformCompletionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopUniformCompletionTheoremToEventFlow
  fromEventFlow := bishopUniformCompletionTheoremFromEventFlow

instance bishopUniformCompletionTheoremChapterTasteGate :
    ChapterTasteGate BishopUniformCompletionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopUniformCompletionTheoremFromEventFlow
          (bishopUniformCompletionTheoremToEventFlow x) =
        some x
    exact BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem BishopUniformCompletionTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        bishopUniformCompletionTheoremDecodeBHist
            (bishopUniformCompletionTheoremEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier BishopUniformCompletionTheoremUp) ∧
        Nonempty (ChapterTasteGate BishopUniformCompletionTheoremUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopUniformCompletionTheoremTasteGate_single_carrier_alignment_decode,
      ⟨bishopUniformCompletionTheoremBHistCarrier⟩,
      ⟨bishopUniformCompletionTheoremChapterTasteGate⟩⟩

end BEDC.Derived.BishopUniformCompletionTheoremUp
