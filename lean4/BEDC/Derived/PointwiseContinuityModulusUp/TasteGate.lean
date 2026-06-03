import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PointwiseContinuityModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PointwiseContinuityModulusUp : Type where
  | mk (X Y F x epsilon delta R U K H C Q N : BHist) : PointwiseContinuityModulusUp
  deriving DecidableEq

def pointwiseContinuityModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pointwiseContinuityModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pointwiseContinuityModulusEncodeBHist h

def pointwiseContinuityModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pointwiseContinuityModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pointwiseContinuityModulusDecodeBHist tail)

private theorem PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def pointwiseContinuityModulusToEventFlow :
    PointwiseContinuityModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PointwiseContinuityModulusUp.mk X Y F x epsilon delta R U K H C Q N =>
      [pointwiseContinuityModulusEncodeBHist X,
        pointwiseContinuityModulusEncodeBHist Y,
        pointwiseContinuityModulusEncodeBHist F,
        pointwiseContinuityModulusEncodeBHist x,
        pointwiseContinuityModulusEncodeBHist epsilon,
        pointwiseContinuityModulusEncodeBHist delta,
        pointwiseContinuityModulusEncodeBHist R,
        pointwiseContinuityModulusEncodeBHist U,
        pointwiseContinuityModulusEncodeBHist K,
        pointwiseContinuityModulusEncodeBHist H,
        pointwiseContinuityModulusEncodeBHist C,
        pointwiseContinuityModulusEncodeBHist Q,
        pointwiseContinuityModulusEncodeBHist N]

private def pointwiseContinuityModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pointwiseContinuityModulusEventAtDefault index rest

def pointwiseContinuityModulusFromEventFlow
    (ef : EventFlow) : Option PointwiseContinuityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PointwiseContinuityModulusUp.mk
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 0 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 1 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 2 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 3 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 4 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 5 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 6 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 7 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 8 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 9 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 10 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 11 ef))
      (pointwiseContinuityModulusDecodeBHist
        (pointwiseContinuityModulusEventAtDefault 12 ef)))

private theorem PointwiseContinuityModulusTasteGate_single_carrier_alignment_round_trip
    (p : PointwiseContinuityModulusUp) :
    pointwiseContinuityModulusFromEventFlow
      (pointwiseContinuityModulusToEventFlow p) = some p := by
  -- BEDC touchpoint anchor: BHist BMark
  cases p with
  | mk X Y F x epsilon delta R U K H C Q N =>
      change
        some
          (PointwiseContinuityModulusUp.mk
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist X))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist Y))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist F))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist x))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist epsilon))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist delta))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist R))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist U))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist K))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist H))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist C))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist Q))
            (pointwiseContinuityModulusDecodeBHist
              (pointwiseContinuityModulusEncodeBHist N))) =
          some (PointwiseContinuityModulusUp.mk X Y F x epsilon delta R U K H C Q N)
      rw [PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode X,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode Y,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode F,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode x,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode epsilon,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode delta,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode R,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode U,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode K,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode H,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode C,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode Q,
        PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode N]

private theorem pointwiseContinuityModulusToEventFlow_injective
    {p q : PointwiseContinuityModulusUp} :
    pointwiseContinuityModulusToEventFlow p =
        pointwiseContinuityModulusToEventFlow q →
      p = q := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pointwiseContinuityModulusFromEventFlow
          (pointwiseContinuityModulusToEventFlow p) =
        pointwiseContinuityModulusFromEventFlow
          (pointwiseContinuityModulusToEventFlow q) :=
    congrArg pointwiseContinuityModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PointwiseContinuityModulusTasteGate_single_carrier_alignment_round_trip p).symm
      (Eq.trans hread
        (PointwiseContinuityModulusTasteGate_single_carrier_alignment_round_trip q)))

instance pointwiseContinuityModulusBHistCarrier :
    BHistCarrier PointwiseContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pointwiseContinuityModulusToEventFlow
  fromEventFlow := pointwiseContinuityModulusFromEventFlow

instance pointwiseContinuityModulusChapterTasteGate :
    ChapterTasteGate PointwiseContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      pointwiseContinuityModulusFromEventFlow
        (pointwiseContinuityModulusToEventFlow x) = some x
    exact PointwiseContinuityModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pointwiseContinuityModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PointwiseContinuityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pointwiseContinuityModulusChapterTasteGate

theorem PointwiseContinuityModulusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PointwiseContinuityModulusUp) ∧
      Nonempty (ChapterTasteGate PointwiseContinuityModulusUp) ∧
      (∀ h : BHist,
        pointwiseContinuityModulusDecodeBHist
          (pointwiseContinuityModulusEncodeBHist h) = h) ∧
      (∀ x : PointwiseContinuityModulusUp,
        pointwiseContinuityModulusFromEventFlow
          (pointwiseContinuityModulusToEventFlow x) = some x) ∧
      pointwiseContinuityModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨pointwiseContinuityModulusBHistCarrier⟩
  constructor
  · exact ⟨pointwiseContinuityModulusChapterTasteGate⟩
  constructor
  · exact PointwiseContinuityModulusTasteGate_single_carrier_alignment_decode
  constructor
  · exact PointwiseContinuityModulusTasteGate_single_carrier_alignment_round_trip
  · rfl

end BEDC.Derived.PointwiseContinuityModulusUp
