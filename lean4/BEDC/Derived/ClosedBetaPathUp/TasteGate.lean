import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBetaPathUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBetaPathUp : Type where
  | mk (s t n B K H C P N : BHist) : ClosedBetaPathUp
  deriving DecidableEq

def closedBetaPathEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBetaPathEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBetaPathEncodeBHist h

def closedBetaPathDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBetaPathDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBetaPathDecodeBHist tail)

private theorem ClosedBetaPathTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, closedBetaPathDecodeBHist (closedBetaPathEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ClosedBetaPathTasteGate_single_carrier_alignment_fields :
    ClosedBetaPathUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBetaPathUp.mk s t n B K H C P N => [s, t, n, B, K, H, C, P, N]

def ClosedBetaPathTasteGate_single_carrier_alignment_toEventFlow :
    ClosedBetaPathUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (ClosedBetaPathTasteGate_single_carrier_alignment_fields x).map
        closedBetaPathEncodeBHist

private def ClosedBetaPathTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ClosedBetaPathTasteGate_single_carrier_alignment_eventAt index rest

def ClosedBetaPathTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option ClosedBetaPathUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedBetaPathUp.mk
      (closedBetaPathDecodeBHist
        (ClosedBetaPathTasteGate_single_carrier_alignment_eventAt 0 ef))
      (closedBetaPathDecodeBHist
        (ClosedBetaPathTasteGate_single_carrier_alignment_eventAt 1 ef))
      (closedBetaPathDecodeBHist
        (ClosedBetaPathTasteGate_single_carrier_alignment_eventAt 2 ef))
      (closedBetaPathDecodeBHist
        (ClosedBetaPathTasteGate_single_carrier_alignment_eventAt 3 ef))
      (closedBetaPathDecodeBHist
        (ClosedBetaPathTasteGate_single_carrier_alignment_eventAt 4 ef))
      (closedBetaPathDecodeBHist
        (ClosedBetaPathTasteGate_single_carrier_alignment_eventAt 5 ef))
      (closedBetaPathDecodeBHist
        (ClosedBetaPathTasteGate_single_carrier_alignment_eventAt 6 ef))
      (closedBetaPathDecodeBHist
        (ClosedBetaPathTasteGate_single_carrier_alignment_eventAt 7 ef))
      (closedBetaPathDecodeBHist
        (ClosedBetaPathTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem ClosedBetaPathTasteGate_single_carrier_alignment_round_trip
    (x : ClosedBetaPathUp) :
    ClosedBetaPathTasteGate_single_carrier_alignment_fromEventFlow
      (ClosedBetaPathTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk s t n B K H C P N =>
      change
        some
          (ClosedBetaPathUp.mk
            (closedBetaPathDecodeBHist (closedBetaPathEncodeBHist s))
            (closedBetaPathDecodeBHist (closedBetaPathEncodeBHist t))
            (closedBetaPathDecodeBHist (closedBetaPathEncodeBHist n))
            (closedBetaPathDecodeBHist (closedBetaPathEncodeBHist B))
            (closedBetaPathDecodeBHist (closedBetaPathEncodeBHist K))
            (closedBetaPathDecodeBHist (closedBetaPathEncodeBHist H))
            (closedBetaPathDecodeBHist (closedBetaPathEncodeBHist C))
            (closedBetaPathDecodeBHist (closedBetaPathEncodeBHist P))
            (closedBetaPathDecodeBHist (closedBetaPathEncodeBHist N))) =
          some (ClosedBetaPathUp.mk s t n B K H C P N)
      rw [ClosedBetaPathTasteGate_single_carrier_alignment_decode s,
        ClosedBetaPathTasteGate_single_carrier_alignment_decode t,
        ClosedBetaPathTasteGate_single_carrier_alignment_decode n,
        ClosedBetaPathTasteGate_single_carrier_alignment_decode B,
        ClosedBetaPathTasteGate_single_carrier_alignment_decode K,
        ClosedBetaPathTasteGate_single_carrier_alignment_decode H,
        ClosedBetaPathTasteGate_single_carrier_alignment_decode C,
        ClosedBetaPathTasteGate_single_carrier_alignment_decode P,
        ClosedBetaPathTasteGate_single_carrier_alignment_decode N]

private theorem ClosedBetaPathTasteGate_single_carrier_alignment_injective
    {x y : ClosedBetaPathUp} :
    ClosedBetaPathTasteGate_single_carrier_alignment_toEventFlow x =
      ClosedBetaPathTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ClosedBetaPathTasteGate_single_carrier_alignment_fromEventFlow
          (ClosedBetaPathTasteGate_single_carrier_alignment_toEventFlow x) =
        ClosedBetaPathTasteGate_single_carrier_alignment_fromEventFlow
          (ClosedBetaPathTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ClosedBetaPathTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedBetaPathTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ClosedBetaPathTasteGate_single_carrier_alignment_round_trip y)))

instance ClosedBetaPathTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier ClosedBetaPathUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ClosedBetaPathTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ClosedBetaPathTasteGate_single_carrier_alignment_fromEventFlow

instance ClosedBetaPathTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate ClosedBetaPathUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ClosedBetaPathTasteGate_single_carrier_alignment_fromEventFlow
        (ClosedBetaPathTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact ClosedBetaPathTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedBetaPathTasteGate_single_carrier_alignment_injective heq)

theorem ClosedBetaPathTasteGate_single_carrier_alignment :
    (forall h : BHist, closedBetaPathDecodeBHist (closedBetaPathEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ClosedBetaPathUp) ∧
        Nonempty (ChapterTasteGate ClosedBetaPathUp) ∧
          closedBetaPathEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ClosedBetaPathTasteGate_single_carrier_alignment_decode,
      ⟨ClosedBetaPathTasteGate_single_carrier_alignment_BHistCarrier⟩,
      ⟨ClosedBetaPathTasteGate_single_carrier_alignment_ChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ClosedBetaPathUp
