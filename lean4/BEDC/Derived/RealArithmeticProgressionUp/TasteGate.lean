import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealArithmeticProgressionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealArithmeticProgressionUp : Type where
  | mk (a d S R D H C P N : BHist) : RealArithmeticProgressionUp
  deriving DecidableEq

def realArithmeticProgressionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realArithmeticProgressionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realArithmeticProgressionEncodeBHist h

def realArithmeticProgressionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realArithmeticProgressionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realArithmeticProgressionDecodeBHist tail)

private theorem RealArithmeticProgressionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realArithmeticProgressionFields :
    RealArithmeticProgressionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealArithmeticProgressionUp.mk a d S R D H C P N => [a, d, S, R, D, H, C, P, N]

def realArithmeticProgressionToEventFlow :
    RealArithmeticProgressionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realArithmeticProgressionFields x).map realArithmeticProgressionEncodeBHist

private def realArithmeticProgressionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realArithmeticProgressionEventAtDefault index rest

def realArithmeticProgressionFromEventFlow
    (ef : EventFlow) : Option RealArithmeticProgressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealArithmeticProgressionUp.mk
      (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 0 ef))
      (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 1 ef))
      (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 2 ef))
      (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 3 ef))
      (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 4 ef))
      (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 5 ef))
      (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 6 ef))
      (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 7 ef))
      (realArithmeticProgressionDecodeBHist (realArithmeticProgressionEventAtDefault 8 ef)))

private theorem RealArithmeticProgressionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealArithmeticProgressionUp,
      realArithmeticProgressionFromEventFlow (realArithmeticProgressionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a d S R D H C P N =>
      change
        some
          (RealArithmeticProgressionUp.mk
            (realArithmeticProgressionDecodeBHist
              (realArithmeticProgressionEncodeBHist a))
            (realArithmeticProgressionDecodeBHist
              (realArithmeticProgressionEncodeBHist d))
            (realArithmeticProgressionDecodeBHist
              (realArithmeticProgressionEncodeBHist S))
            (realArithmeticProgressionDecodeBHist
              (realArithmeticProgressionEncodeBHist R))
            (realArithmeticProgressionDecodeBHist
              (realArithmeticProgressionEncodeBHist D))
            (realArithmeticProgressionDecodeBHist
              (realArithmeticProgressionEncodeBHist H))
            (realArithmeticProgressionDecodeBHist
              (realArithmeticProgressionEncodeBHist C))
            (realArithmeticProgressionDecodeBHist
              (realArithmeticProgressionEncodeBHist P))
            (realArithmeticProgressionDecodeBHist
              (realArithmeticProgressionEncodeBHist N))) =
          some (RealArithmeticProgressionUp.mk a d S R D H C P N)
      rw [RealArithmeticProgressionTasteGate_single_carrier_alignment_decode a,
        RealArithmeticProgressionTasteGate_single_carrier_alignment_decode d,
        RealArithmeticProgressionTasteGate_single_carrier_alignment_decode S,
        RealArithmeticProgressionTasteGate_single_carrier_alignment_decode R,
        RealArithmeticProgressionTasteGate_single_carrier_alignment_decode D,
        RealArithmeticProgressionTasteGate_single_carrier_alignment_decode H,
        RealArithmeticProgressionTasteGate_single_carrier_alignment_decode C,
        RealArithmeticProgressionTasteGate_single_carrier_alignment_decode P,
        RealArithmeticProgressionTasteGate_single_carrier_alignment_decode N]

private theorem RealArithmeticProgressionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealArithmeticProgressionUp} :
    realArithmeticProgressionToEventFlow x = realArithmeticProgressionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realArithmeticProgressionFromEventFlow (realArithmeticProgressionToEventFlow x) =
        realArithmeticProgressionFromEventFlow (realArithmeticProgressionToEventFlow y) :=
    congrArg realArithmeticProgressionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealArithmeticProgressionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealArithmeticProgressionTasteGate_single_carrier_alignment_round_trip y)))

instance realArithmeticProgressionBHistCarrier :
    BHistCarrier RealArithmeticProgressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realArithmeticProgressionToEventFlow
  fromEventFlow := realArithmeticProgressionFromEventFlow

instance realArithmeticProgressionChapterTasteGate :
    ChapterTasteGate RealArithmeticProgressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realArithmeticProgressionFromEventFlow (realArithmeticProgressionToEventFlow x) =
        some x
    exact RealArithmeticProgressionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealArithmeticProgressionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealArithmeticProgressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realArithmeticProgressionChapterTasteGate

theorem RealArithmeticProgressionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      realArithmeticProgressionDecodeBHist (realArithmeticProgressionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealArithmeticProgressionUp) ∧
        Nonempty (ChapterTasteGate RealArithmeticProgressionUp) ∧
          realArithmeticProgressionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealArithmeticProgressionTasteGate_single_carrier_alignment_decode,
      ⟨realArithmeticProgressionBHistCarrier⟩,
      ⟨realArithmeticProgressionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealArithmeticProgressionUp.TasteGate
