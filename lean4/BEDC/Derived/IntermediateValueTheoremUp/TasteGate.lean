import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntermediateValueTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntermediateValueTheoremUp : Type where
  | mk (I J F A B S R E H C P N : BHist) : IntermediateValueTheoremUp
  deriving DecidableEq

def intermediateValueTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intermediateValueTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intermediateValueTheoremEncodeBHist h

def intermediateValueTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intermediateValueTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intermediateValueTheoremDecodeBHist tail)

private theorem IntermediateValueTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intermediateValueTheoremFields :
    IntermediateValueTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntermediateValueTheoremUp.mk I J F A B S R E H C P N =>
      [I, J, F, A, B, S, R, E, H, C, P, N]

def intermediateValueTheoremToEventFlow :
    IntermediateValueTheoremUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (intermediateValueTheoremFields x).map intermediateValueTheoremEncodeBHist

private def intermediateValueTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => intermediateValueTheoremEventAtDefault index rest

def intermediateValueTheoremFromEventFlow
    (ef : EventFlow) : Option IntermediateValueTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntermediateValueTheoremUp.mk
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 0 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 1 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 2 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 3 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 4 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 5 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 6 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 7 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 8 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 9 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 10 ef))
      (intermediateValueTheoremDecodeBHist
        (intermediateValueTheoremEventAtDefault 11 ef)))

private theorem IntermediateValueTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IntermediateValueTheoremUp,
      intermediateValueTheoremFromEventFlow (intermediateValueTheoremToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J F A B S R E H C P N =>
      change
        some
          (IntermediateValueTheoremUp.mk
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist I))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist J))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist F))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist A))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist B))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist S))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist R))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist E))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist H))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist C))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist P))
            (intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist N))) =
          some (IntermediateValueTheoremUp.mk I J F A B S R E H C P N)
      rw [IntermediateValueTheoremTasteGate_single_carrier_alignment_decode I,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode J,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode F,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode A,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode B,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode S,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode R,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode E,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode H,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode C,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode P,
        IntermediateValueTheoremTasteGate_single_carrier_alignment_decode N]

private theorem IntermediateValueTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IntermediateValueTheoremUp} :
    intermediateValueTheoremToEventFlow x =
      intermediateValueTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intermediateValueTheoremFromEventFlow (intermediateValueTheoremToEventFlow x) =
        intermediateValueTheoremFromEventFlow (intermediateValueTheoremToEventFlow y) :=
    congrArg intermediateValueTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (IntermediateValueTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (IntermediateValueTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance intermediateValueTheoremBHistCarrier :
    BHistCarrier IntermediateValueTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intermediateValueTheoremToEventFlow
  fromEventFlow := intermediateValueTheoremFromEventFlow

instance intermediateValueTheoremChapterTasteGate :
    ChapterTasteGate IntermediateValueTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      intermediateValueTheoremFromEventFlow (intermediateValueTheoremToEventFlow x) =
        some x
    exact IntermediateValueTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntermediateValueTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate IntermediateValueTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  intermediateValueTheoremChapterTasteGate

theorem IntermediateValueTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      intermediateValueTheoremDecodeBHist (intermediateValueTheoremEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier IntermediateValueTheoremUp) ∧
        Nonempty (ChapterTasteGate IntermediateValueTheoremUp) ∧
          intermediateValueTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨IntermediateValueTheoremTasteGate_single_carrier_alignment_decode,
      ⟨intermediateValueTheoremBHistCarrier⟩,
      ⟨intermediateValueTheoremChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.IntermediateValueTheoremUp
