import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StokesTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StokesTheoremUp : Type where
  | mk (M F B E I H C P N : BHist) : StokesTheoremUp
  deriving DecidableEq

def stokesTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stokesTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stokesTheoremEncodeBHist h

def stokesTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stokesTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stokesTheoremDecodeBHist tail)

private theorem StokesTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, stokesTheoremDecodeBHist (stokesTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stokesTheoremToEventFlow : StokesTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StokesTheoremUp.mk M F B E I H C P N =>
      [stokesTheoremEncodeBHist M,
        stokesTheoremEncodeBHist F,
        stokesTheoremEncodeBHist B,
        stokesTheoremEncodeBHist E,
        stokesTheoremEncodeBHist I,
        stokesTheoremEncodeBHist H,
        stokesTheoremEncodeBHist C,
        stokesTheoremEncodeBHist P,
        stokesTheoremEncodeBHist N]

private def stokesTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => stokesTheoremEventAtDefault index rest

def stokesTheoremFromEventFlow : EventFlow → Option StokesTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (StokesTheoremUp.mk
        (stokesTheoremDecodeBHist (stokesTheoremEventAtDefault 0 ef))
        (stokesTheoremDecodeBHist (stokesTheoremEventAtDefault 1 ef))
        (stokesTheoremDecodeBHist (stokesTheoremEventAtDefault 2 ef))
        (stokesTheoremDecodeBHist (stokesTheoremEventAtDefault 3 ef))
        (stokesTheoremDecodeBHist (stokesTheoremEventAtDefault 4 ef))
        (stokesTheoremDecodeBHist (stokesTheoremEventAtDefault 5 ef))
        (stokesTheoremDecodeBHist (stokesTheoremEventAtDefault 6 ef))
        (stokesTheoremDecodeBHist (stokesTheoremEventAtDefault 7 ef))
        (stokesTheoremDecodeBHist (stokesTheoremEventAtDefault 8 ef)))

private theorem StokesTheoremTasteGate_single_carrier_alignment_round_trip
    (x : StokesTheoremUp) :
    stokesTheoremFromEventFlow (stokesTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M F B E I H C P N =>
      change
        some
            (StokesTheoremUp.mk
              (stokesTheoremDecodeBHist (stokesTheoremEncodeBHist M))
              (stokesTheoremDecodeBHist (stokesTheoremEncodeBHist F))
              (stokesTheoremDecodeBHist (stokesTheoremEncodeBHist B))
              (stokesTheoremDecodeBHist (stokesTheoremEncodeBHist E))
              (stokesTheoremDecodeBHist (stokesTheoremEncodeBHist I))
              (stokesTheoremDecodeBHist (stokesTheoremEncodeBHist H))
              (stokesTheoremDecodeBHist (stokesTheoremEncodeBHist C))
              (stokesTheoremDecodeBHist (stokesTheoremEncodeBHist P))
              (stokesTheoremDecodeBHist (stokesTheoremEncodeBHist N))) =
          some (StokesTheoremUp.mk M F B E I H C P N)
      rw [StokesTheoremTasteGate_single_carrier_alignment_decode_encode M,
        StokesTheoremTasteGate_single_carrier_alignment_decode_encode F,
        StokesTheoremTasteGate_single_carrier_alignment_decode_encode B,
        StokesTheoremTasteGate_single_carrier_alignment_decode_encode E,
        StokesTheoremTasteGate_single_carrier_alignment_decode_encode I,
        StokesTheoremTasteGate_single_carrier_alignment_decode_encode H,
        StokesTheoremTasteGate_single_carrier_alignment_decode_encode C,
        StokesTheoremTasteGate_single_carrier_alignment_decode_encode P,
        StokesTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem StokesTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StokesTheoremUp} :
    stokesTheoremToEventFlow x = stokesTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stokesTheoremFromEventFlow (stokesTheoremToEventFlow x) =
        stokesTheoremFromEventFlow (stokesTheoremToEventFlow y) :=
    congrArg stokesTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (StokesTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StokesTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance stokesTheoremBHistCarrier : BHistCarrier StokesTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stokesTheoremToEventFlow
  fromEventFlow := stokesTheoremFromEventFlow

instance stokesTheoremChapterTasteGate : ChapterTasteGate StokesTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change stokesTheoremFromEventFlow (stokesTheoremToEventFlow x) = some x
    exact StokesTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StokesTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate StokesTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stokesTheoremChapterTasteGate

theorem StokesTheoremTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier StokesTheoremUp,
      Nonempty (@ChapterTasteGate StokesTheoremUp carrier)) ∧
      (∀ h : BHist, stokesTheoremDecodeBHist (stokesTheoremEncodeBHist h) = h) ∧
        (∀ x : StokesTheoremUp,
          stokesTheoremFromEventFlow (stokesTheoremToEventFlow x) = some x) ∧
          stokesTheoremEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨stokesTheoremBHistCarrier, ⟨stokesTheoremChapterTasteGate⟩⟩,
      StokesTheoremTasteGate_single_carrier_alignment_decode_encode,
      StokesTheoremTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.StokesTheoremUp
