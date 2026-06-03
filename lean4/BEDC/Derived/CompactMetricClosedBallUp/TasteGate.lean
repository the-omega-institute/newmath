import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricClosedBallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactMetricClosedBallUp : Type where
  | mk (X c r M F T C H P N : BHist) : CompactMetricClosedBallUp
  deriving DecidableEq

def compactMetricClosedBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactMetricClosedBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactMetricClosedBallEncodeBHist h

def compactMetricClosedBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactMetricClosedBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactMetricClosedBallDecodeBHist tail)

private theorem CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactMetricClosedBallFields : CompactMetricClosedBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricClosedBallUp.mk X c r M F T C H P N => [X, c, r, M, F, T, C, H, P, N]

def compactMetricClosedBallToEventFlow : CompactMetricClosedBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactMetricClosedBallFields x).map compactMetricClosedBallEncodeBHist

private def compactMetricClosedBallEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactMetricClosedBallEventAt index rest

def compactMetricClosedBallFromEventFlow (ef : EventFlow) :
    Option CompactMetricClosedBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactMetricClosedBallUp.mk
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 0 ef))
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 1 ef))
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 2 ef))
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 3 ef))
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 4 ef))
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 5 ef))
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 6 ef))
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 7 ef))
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 8 ef))
      (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEventAt 9 ef)))

private theorem CompactMetricClosedBallTasteGate_single_carrier_alignment_round_trip
    (x : CompactMetricClosedBallUp) :
    compactMetricClosedBallFromEventFlow (compactMetricClosedBallToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X c r M F T C H P N =>
      change
        some
          (CompactMetricClosedBallUp.mk
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist X))
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist c))
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist r))
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist M))
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist F))
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist T))
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist C))
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist H))
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist P))
            (compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist N))) =
          some (CompactMetricClosedBallUp.mk X c r M F T C H P N)
      rw [CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode X,
        CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode c,
        CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode r,
        CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode M,
        CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode F,
        CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode T,
        CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode C,
        CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode H,
        CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode P,
        CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactMetricClosedBallTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactMetricClosedBallUp} :
    compactMetricClosedBallToEventFlow x = compactMetricClosedBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactMetricClosedBallFromEventFlow (compactMetricClosedBallToEventFlow x) =
        compactMetricClosedBallFromEventFlow (compactMetricClosedBallToEventFlow y) :=
    congrArg compactMetricClosedBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactMetricClosedBallTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactMetricClosedBallTasteGate_single_carrier_alignment_round_trip y)))

instance compactMetricClosedBallBHistCarrier :
    BHistCarrier CompactMetricClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactMetricClosedBallToEventFlow
  fromEventFlow := compactMetricClosedBallFromEventFlow

instance compactMetricClosedBallChapterTasteGate :
    ChapterTasteGate CompactMetricClosedBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactMetricClosedBallFromEventFlow (compactMetricClosedBallToEventFlow x) =
        some x
    exact CompactMetricClosedBallTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactMetricClosedBallTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactMetricClosedBallTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactMetricClosedBallDecodeBHist (compactMetricClosedBallEncodeBHist h) = h) ∧
      (∀ x : CompactMetricClosedBallUp,
        compactMetricClosedBallFromEventFlow (compactMetricClosedBallToEventFlow x) =
          some x) ∧
      (∀ x y : CompactMetricClosedBallUp,
        compactMetricClosedBallToEventFlow x = compactMetricClosedBallToEventFlow y →
          x = y) ∧
      compactMetricClosedBallEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactMetricClosedBallTasteGate_single_carrier_alignment_decode_encode,
      CompactMetricClosedBallTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompactMetricClosedBallTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactMetricClosedBallUp
