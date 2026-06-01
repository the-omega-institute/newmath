import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICCriticalPathUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICCriticalPathUp : Type where
  | mk (S N O U D H C P L : BHist) : MetaCICCriticalPathUp
  deriving DecidableEq

def metaCICCriticalPathEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICCriticalPathEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICCriticalPathEncodeBHist h

def metaCICCriticalPathDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICCriticalPathDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICCriticalPathDecodeBHist tail)

private theorem MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICCriticalPathFields : MetaCICCriticalPathUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICCriticalPathUp.mk S N O U D H C P L => [S, N, O, U, D, H, C, P, L]

def metaCICCriticalPathToEventFlow : MetaCICCriticalPathUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICCriticalPathFields x).map metaCICCriticalPathEncodeBHist

private def metaCICCriticalPathEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metaCICCriticalPathEventAt index rest

def metaCICCriticalPathFromEventFlow (ef : EventFlow) : Option MetaCICCriticalPathUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICCriticalPathUp.mk
      (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEventAt 0 ef))
      (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEventAt 1 ef))
      (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEventAt 2 ef))
      (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEventAt 3 ef))
      (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEventAt 4 ef))
      (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEventAt 5 ef))
      (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEventAt 6 ef))
      (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEventAt 7 ef))
      (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEventAt 8 ef)))

private theorem MetaCICCriticalPathTasteGate_single_carrier_alignment_round_trip
    (x : MetaCICCriticalPathUp) :
    metaCICCriticalPathFromEventFlow (metaCICCriticalPathToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S N O U D H C P L =>
      change
        some
          (MetaCICCriticalPathUp.mk
            (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist S))
            (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist N))
            (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist O))
            (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist U))
            (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist D))
            (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist H))
            (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist C))
            (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist P))
            (metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist L))) =
          some (MetaCICCriticalPathUp.mk S N O U D H C P L)
      rw [MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode S,
        MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode N,
        MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode O,
        MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode U,
        MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode D,
        MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode H,
        MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode C,
        MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode P,
        MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode L]

private theorem MetaCICCriticalPathTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetaCICCriticalPathUp} :
    metaCICCriticalPathToEventFlow x = metaCICCriticalPathToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICCriticalPathFromEventFlow (metaCICCriticalPathToEventFlow x) =
        metaCICCriticalPathFromEventFlow (metaCICCriticalPathToEventFlow y) :=
    congrArg metaCICCriticalPathFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetaCICCriticalPathTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetaCICCriticalPathTasteGate_single_carrier_alignment_round_trip y)))

instance metaCICCriticalPathBHistCarrier : BHistCarrier MetaCICCriticalPathUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICCriticalPathToEventFlow
  fromEventFlow := metaCICCriticalPathFromEventFlow

instance metaCICCriticalPathChapterTasteGate : ChapterTasteGate MetaCICCriticalPathUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaCICCriticalPathFromEventFlow (metaCICCriticalPathToEventFlow x) = some x
    exact MetaCICCriticalPathTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetaCICCriticalPathTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def MetaCICCriticalPathTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MetaCICCriticalPathUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICCriticalPathChapterTasteGate

theorem MetaCICCriticalPathTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICCriticalPathDecodeBHist (metaCICCriticalPathEncodeBHist h) = h) ∧
      (∀ x : MetaCICCriticalPathUp,
        metaCICCriticalPathFromEventFlow (metaCICCriticalPathToEventFlow x) = some x) ∧
        (∀ x y : MetaCICCriticalPathUp,
          metaCICCriticalPathToEventFlow x = metaCICCriticalPathToEventFlow y → x = y) ∧
          metaCICCriticalPathEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MetaCICCriticalPathTasteGate_single_carrier_alignment_decode_encode,
      MetaCICCriticalPathTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MetaCICCriticalPathTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICCriticalPathUp.TasteGate
