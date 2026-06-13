import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationReplayUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationReplayUp : Type where
  | mk (S T E H C P N : BHist) : ContinuationReplayUp
  deriving DecidableEq

private def encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode :
    forall h : BHist, decodeBHist (encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def fields : ContinuationReplayUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationReplayUp.mk S T E H C P N => [S, T, E, H, C, P, N]

private def toEventFlow : ContinuationReplayUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fields x).map encodeBHist

private def eventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eventAt index rest

private def fromEventFlow (ef : EventFlow) : Option ContinuationReplayUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuationReplayUp.mk
      (decodeBHist (eventAt 0 ef))
      (decodeBHist (eventAt 1 ef))
      (decodeBHist (eventAt 2 ef))
      (decodeBHist (eventAt 3 ef))
      (decodeBHist (eventAt 4 ef))
      (decodeBHist (eventAt 5 ef))
      (decodeBHist (eventAt 6 ef)))

private theorem round_trip (x : ContinuationReplayUp) :
    fromEventFlow (toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T E H C P N =>
      change
        some
          (ContinuationReplayUp.mk
            (decodeBHist (encodeBHist S))
            (decodeBHist (encodeBHist T))
            (decodeBHist (encodeBHist E))
            (decodeBHist (encodeBHist H))
            (decodeBHist (encodeBHist C))
            (decodeBHist (encodeBHist P))
            (decodeBHist (encodeBHist N))) =
          some (ContinuationReplayUp.mk S T E H C P N)
      rw [decode_encode S, decode_encode T, decode_encode E, decode_encode H,
        decode_encode C, decode_encode P, decode_encode N]

private theorem toEventFlow_injective {x y : ContinuationReplayUp} :
    toEventFlow x = toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : fromEventFlow (toEventFlow x) = fromEventFlow (toEventFlow y) :=
    congrArg fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (round_trip x).symm (Eq.trans hread (round_trip y)))

private theorem fields_faithful :
    forall x y : ContinuationReplayUp, fields x = fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance continuationReplayBHistCarrier : BHistCarrier ContinuationReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := toEventFlow
  fromEventFlow := fromEventFlow

instance continuationReplayChapterTasteGate : ChapterTasteGate ContinuationReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fromEventFlow (toEventFlow x) = some x
    exact round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (toEventFlow_injective heq)

instance continuationReplayFieldFaithful : FieldFaithful ContinuationReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fields
  field_faithful := fields_faithful

instance continuationReplayNontrivial : Nontrivial ContinuationReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContinuationReplayUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ContinuationReplayUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ContinuationReplayTasteGate_single_carrier_alignment :
    ChapterTasteGate ContinuationReplayUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact continuationReplayChapterTasteGate

end BEDC.Derived.ContinuationReplayUp.TasteGate
