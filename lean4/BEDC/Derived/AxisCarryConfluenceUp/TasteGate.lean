import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisCarryConfluenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisCarryConfluenceUp : Type where
  | mk
      (u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow :
        BHist) : AxisCarryConfluenceUp
  deriving DecidableEq

def axisCarryConfluenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisCarryConfluenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisCarryConfluenceEncodeBHist h

def axisCarryConfluenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisCarryConfluenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisCarryConfluenceDecodeBHist tail)

private theorem AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def axisCarryConfluenceFields : AxisCarryConfluenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AxisCarryConfluenceUp.mk u v w n routeLeft routeRight valueLedger boundary continuation
      provenance nameRow =>
      [u, v, w, n, routeLeft, routeRight, valueLedger, boundary, continuation, provenance,
        nameRow]

def axisCarryConfluenceToEventFlow : AxisCarryConfluenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (axisCarryConfluenceFields x).map axisCarryConfluenceEncodeBHist

private def axisCarryConfluenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => axisCarryConfluenceEventAt index rest

def axisCarryConfluenceFromEventFlow
    (ef : EventFlow) : Option AxisCarryConfluenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AxisCarryConfluenceUp.mk
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 0 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 1 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 2 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 3 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 4 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 5 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 6 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 7 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 8 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 9 ef))
      (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEventAt 10 ef)))

private theorem AxisCarryConfluenceTasteGate_single_carrier_alignment_round_trip
    (x : AxisCarryConfluenceUp) :
    axisCarryConfluenceFromEventFlow (axisCarryConfluenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk u v w n routeLeft routeRight valueLedger boundary continuation provenance nameRow =>
      change
        some
          (AxisCarryConfluenceUp.mk
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist u))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist v))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist w))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist n))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist routeLeft))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist routeRight))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist valueLedger))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist boundary))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist continuation))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist provenance))
            (axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist nameRow))) =
          some
            (AxisCarryConfluenceUp.mk u v w n routeLeft routeRight valueLedger boundary
              continuation provenance nameRow)
      rw [AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode u,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode v,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode w,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode n,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode routeLeft,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode routeRight,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode valueLedger,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode boundary,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode continuation,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode provenance,
        AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode nameRow]

private theorem AxisCarryConfluenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AxisCarryConfluenceUp} :
    axisCarryConfluenceToEventFlow x = axisCarryConfluenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisCarryConfluenceFromEventFlow (axisCarryConfluenceToEventFlow x) =
        axisCarryConfluenceFromEventFlow (axisCarryConfluenceToEventFlow y) :=
    congrArg axisCarryConfluenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AxisCarryConfluenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AxisCarryConfluenceTasteGate_single_carrier_alignment_round_trip y)))

instance axisCarryConfluenceBHistCarrier : BHistCarrier AxisCarryConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisCarryConfluenceToEventFlow
  fromEventFlow := axisCarryConfluenceFromEventFlow

instance axisCarryConfluenceChapterTasteGate :
    ChapterTasteGate AxisCarryConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axisCarryConfluenceFromEventFlow (axisCarryConfluenceToEventFlow x) = some x
    exact AxisCarryConfluenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AxisCarryConfluenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AxisCarryConfluenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, axisCarryConfluenceDecodeBHist (axisCarryConfluenceEncodeBHist h) = h) ∧
      (∀ x : AxisCarryConfluenceUp,
        axisCarryConfluenceFromEventFlow (axisCarryConfluenceToEventFlow x) = some x) ∧
        (∀ x y : AxisCarryConfluenceUp,
          axisCarryConfluenceToEventFlow x = axisCarryConfluenceToEventFlow y → x = y) ∧
          axisCarryConfluenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨AxisCarryConfluenceTasteGate_single_carrier_alignment_decode_encode,
      AxisCarryConfluenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        AxisCarryConfluenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AxisCarryConfluenceUp
