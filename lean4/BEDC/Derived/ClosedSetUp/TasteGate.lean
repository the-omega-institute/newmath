import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedSetUp : Type where
  | mk (T M S F O B H C P N : BHist) : ClosedSetUp
  deriving DecidableEq

def closedSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedSetEncodeBHist h

def closedSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedSetDecodeBHist tail)

private theorem ClosedSetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, closedSetDecodeBHist (closedSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedSetFields : ClosedSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedSetUp.mk T M S F O B H C P N => [T, M, S, F, O, B, H, C, P, N]

def closedSetToEventFlow : ClosedSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map closedSetEncodeBHist (closedSetFields x)

private def closedSetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedSetEventAt index rest

def closedSetFromEventFlow : EventFlow → Option ClosedSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ClosedSetUp.mk
          (closedSetDecodeBHist (closedSetEventAt 0 ef))
          (closedSetDecodeBHist (closedSetEventAt 1 ef))
          (closedSetDecodeBHist (closedSetEventAt 2 ef))
          (closedSetDecodeBHist (closedSetEventAt 3 ef))
          (closedSetDecodeBHist (closedSetEventAt 4 ef))
          (closedSetDecodeBHist (closedSetEventAt 5 ef))
          (closedSetDecodeBHist (closedSetEventAt 6 ef))
          (closedSetDecodeBHist (closedSetEventAt 7 ef))
          (closedSetDecodeBHist (closedSetEventAt 8 ef))
          (closedSetDecodeBHist (closedSetEventAt 9 ef)))

private theorem ClosedSetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedSetUp, closedSetFromEventFlow (closedSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M S F O B H C P N =>
      change
        some
          (ClosedSetUp.mk
            (closedSetDecodeBHist (closedSetEncodeBHist T))
            (closedSetDecodeBHist (closedSetEncodeBHist M))
            (closedSetDecodeBHist (closedSetEncodeBHist S))
            (closedSetDecodeBHist (closedSetEncodeBHist F))
            (closedSetDecodeBHist (closedSetEncodeBHist O))
            (closedSetDecodeBHist (closedSetEncodeBHist B))
            (closedSetDecodeBHist (closedSetEncodeBHist H))
            (closedSetDecodeBHist (closedSetEncodeBHist C))
            (closedSetDecodeBHist (closedSetEncodeBHist P))
            (closedSetDecodeBHist (closedSetEncodeBHist N))) =
          some (ClosedSetUp.mk T M S F O B H C P N)
      rw [ClosedSetTasteGate_single_carrier_alignment_decode T,
        ClosedSetTasteGate_single_carrier_alignment_decode M,
        ClosedSetTasteGate_single_carrier_alignment_decode S,
        ClosedSetTasteGate_single_carrier_alignment_decode F,
        ClosedSetTasteGate_single_carrier_alignment_decode O,
        ClosedSetTasteGate_single_carrier_alignment_decode B,
        ClosedSetTasteGate_single_carrier_alignment_decode H,
        ClosedSetTasteGate_single_carrier_alignment_decode C,
        ClosedSetTasteGate_single_carrier_alignment_decode P,
        ClosedSetTasteGate_single_carrier_alignment_decode N]

private theorem ClosedSetTasteGate_single_carrier_alignment_injective {x y : ClosedSetUp} :
    closedSetToEventFlow x = closedSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedSetFromEventFlow (closedSetToEventFlow x) =
        closedSetFromEventFlow (closedSetToEventFlow y) :=
    congrArg closedSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ClosedSetTasteGate_single_carrier_alignment_round_trip y)))

instance closedSetBHistCarrier : BHistCarrier ClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedSetToEventFlow
  fromEventFlow := closedSetFromEventFlow

instance closedSetChapterTasteGate : ChapterTasteGate ClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedSetFromEventFlow (closedSetToEventFlow x) = some x
    exact ClosedSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedSetTasteGate_single_carrier_alignment_injective heq)

theorem ClosedSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, closedSetDecodeBHist (closedSetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ClosedSetUp) ∧
        Nonempty (ChapterTasteGate ClosedSetUp) ∧
          closedSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ClosedSetTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ⟨closedSetBHistCarrier⟩
    · constructor
      · exact ⟨closedSetChapterTasteGate⟩
      · rfl

end BEDC.Derived.ClosedSetUp
