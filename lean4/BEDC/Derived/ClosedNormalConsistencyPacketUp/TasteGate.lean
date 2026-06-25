import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedNormalConsistencyPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedNormalConsistencyPacketUp : Type where
  | mk (L T B F K G H C P N : BHist) : ClosedNormalConsistencyPacketUp
  deriving DecidableEq

def closedNormalConsistencyPacketFields :
    ClosedNormalConsistencyPacketUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalConsistencyPacketUp.mk L T B F K G H C P N =>
      [L, T, B, F, K, G, H, C, P, N]

def closedNormalConsistencyPacketEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedNormalConsistencyPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedNormalConsistencyPacketEncodeBHist h

def closedNormalConsistencyPacketDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedNormalConsistencyPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedNormalConsistencyPacketDecodeBHist tail)

theorem ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      closedNormalConsistencyPacketDecodeBHist
          (closedNormalConsistencyPacketEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedNormalConsistencyPacketToEventFlow :
    ClosedNormalConsistencyPacketUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedNormalConsistencyPacketFields x).map closedNormalConsistencyPacketEncodeBHist

private def closedNormalConsistencyPacketEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedNormalConsistencyPacketEventAt index rest

def closedNormalConsistencyPacketFromEventFlow
    (ef : EventFlow) :
    Option ClosedNormalConsistencyPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedNormalConsistencyPacketUp.mk
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 0 ef))
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 1 ef))
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 2 ef))
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 3 ef))
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 4 ef))
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 5 ef))
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 6 ef))
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 7 ef))
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 8 ef))
      (closedNormalConsistencyPacketDecodeBHist
        (closedNormalConsistencyPacketEventAt 9 ef)))

theorem ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_round_trip
    (x : ClosedNormalConsistencyPacketUp) :
    closedNormalConsistencyPacketFromEventFlow
        (closedNormalConsistencyPacketToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L T B F K G H C P N =>
      change
        some
            (ClosedNormalConsistencyPacketUp.mk
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist L))
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist T))
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist B))
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist F))
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist K))
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist G))
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist H))
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist C))
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist P))
              (closedNormalConsistencyPacketDecodeBHist
                (closedNormalConsistencyPacketEncodeBHist N))) =
          some (ClosedNormalConsistencyPacketUp.mk L T B F K G H C P N)
      rw [ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode L,
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode T,
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode B,
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode F,
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode K,
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode G,
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode H,
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode C,
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode P,
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode N]

theorem ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedNormalConsistencyPacketUp} :
    closedNormalConsistencyPacketToEventFlow x =
      closedNormalConsistencyPacketToEventFlow y ->
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalConsistencyPacketFromEventFlow
          (closedNormalConsistencyPacketToEventFlow x) =
        closedNormalConsistencyPacketFromEventFlow
          (closedNormalConsistencyPacketToEventFlow y) :=
    congrArg closedNormalConsistencyPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_round_trip y)))

instance closedNormalConsistencyPacketBHistCarrier :
    BHistCarrier ClosedNormalConsistencyPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalConsistencyPacketToEventFlow
  fromEventFlow := closedNormalConsistencyPacketFromEventFlow

instance closedNormalConsistencyPacketChapterTasteGate :
    ChapterTasteGate ClosedNormalConsistencyPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedNormalConsistencyPacketFromEventFlow
        (closedNormalConsistencyPacketToEventFlow x) =
      some x
    exact ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate ClosedNormalConsistencyPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedNormalConsistencyPacketChapterTasteGate

theorem ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment :
    (forall h : BHist,
      closedNormalConsistencyPacketDecodeBHist
          (closedNormalConsistencyPacketEncodeBHist h) =
        h) /\
      (forall x : ClosedNormalConsistencyPacketUp,
        closedNormalConsistencyPacketFromEventFlow
            (closedNormalConsistencyPacketToEventFlow x) =
          some x) /\
      (forall x y : ClosedNormalConsistencyPacketUp,
        closedNormalConsistencyPacketToEventFlow x =
          closedNormalConsistencyPacketToEventFlow y ->
        x = y) /\
      closedNormalConsistencyPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_decode_encode,
      ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ClosedNormalConsistencyPacketTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.ClosedNormalConsistencyPacketUp
