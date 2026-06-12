import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpperDarbouxSumUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpperDarbouxSumUp : Type where
  | mk (P B D S I R H C Q N : BHist) : UpperDarbouxSumUp
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

private def fields : UpperDarbouxSumUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UpperDarbouxSumUp.mk P B D S I R H C Q N => [P, B, D, S, I, R, H, C, Q, N]

private def toEventFlow : UpperDarbouxSumUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fields x).map encodeBHist

private def eventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eventAt index rest

private def fromEventFlow (ef : EventFlow) : Option UpperDarbouxSumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UpperDarbouxSumUp.mk
      (decodeBHist (eventAt 0 ef))
      (decodeBHist (eventAt 1 ef))
      (decodeBHist (eventAt 2 ef))
      (decodeBHist (eventAt 3 ef))
      (decodeBHist (eventAt 4 ef))
      (decodeBHist (eventAt 5 ef))
      (decodeBHist (eventAt 6 ef))
      (decodeBHist (eventAt 7 ef))
      (decodeBHist (eventAt 8 ef))
      (decodeBHist (eventAt 9 ef)))

private theorem round_trip (x : UpperDarbouxSumUp) :
    fromEventFlow (toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P B D S I R H C Q N =>
      change
        some
          (UpperDarbouxSumUp.mk
            (decodeBHist (encodeBHist P))
            (decodeBHist (encodeBHist B))
            (decodeBHist (encodeBHist D))
            (decodeBHist (encodeBHist S))
            (decodeBHist (encodeBHist I))
            (decodeBHist (encodeBHist R))
            (decodeBHist (encodeBHist H))
            (decodeBHist (encodeBHist C))
            (decodeBHist (encodeBHist Q))
            (decodeBHist (encodeBHist N))) =
          some (UpperDarbouxSumUp.mk P B D S I R H C Q N)
      rw [decode_encode P, decode_encode B, decode_encode D, decode_encode S,
        decode_encode I, decode_encode R, decode_encode H, decode_encode C,
        decode_encode Q, decode_encode N]

private theorem toEventFlow_injective {x y : UpperDarbouxSumUp} :
    toEventFlow x = toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : fromEventFlow (toEventFlow x) = fromEventFlow (toEventFlow y) :=
    congrArg fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (round_trip x).symm (Eq.trans hread (round_trip y)))

private theorem fields_faithful :
    forall x y : UpperDarbouxSumUp, fields x = fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 B1 D1 S1 I1 R1 H1 C1 Q1 N1 =>
      cases y with
      | mk P2 B2 D2 S2 I2 R2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance upperDarbouxSumBHistCarrier : BHistCarrier UpperDarbouxSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := toEventFlow
  fromEventFlow := fromEventFlow

instance upperDarbouxSumChapterTasteGate : ChapterTasteGate UpperDarbouxSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fromEventFlow (toEventFlow x) = some x
    exact round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (toEventFlow_injective heq)

instance upperDarbouxSumFieldFaithful : FieldFaithful UpperDarbouxSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fields
  field_faithful := fields_faithful

instance upperDarbouxSumNontrivial : Nontrivial UpperDarbouxSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UpperDarbouxSumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UpperDarbouxSumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem UpperDarbouxSumTasteGate_single_carrier_alignment :
    ChapterTasteGate UpperDarbouxSumUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact upperDarbouxSumChapterTasteGate

end BEDC.Derived.UpperDarbouxSumUp.TasteGate
