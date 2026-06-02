import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICNormalizationAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICNormalizationAuditPacketUp : Type where
  | mk (T K A S I P F H C G N : BHist) : MetaCICNormalizationAuditPacketUp
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

private def fields : MetaCICNormalizationAuditPacketUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICNormalizationAuditPacketUp.mk T K A S I P F H C G N =>
      [T, K, A, S, I, P, F, H, C, G, N]

private def toEventFlow : MetaCICNormalizationAuditPacketUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fields x).map encodeBHist

private def eventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eventAt index rest

private def fromEventFlow (ef : EventFlow) :
    Option MetaCICNormalizationAuditPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICNormalizationAuditPacketUp.mk
      (decodeBHist (eventAt 0 ef))
      (decodeBHist (eventAt 1 ef))
      (decodeBHist (eventAt 2 ef))
      (decodeBHist (eventAt 3 ef))
      (decodeBHist (eventAt 4 ef))
      (decodeBHist (eventAt 5 ef))
      (decodeBHist (eventAt 6 ef))
      (decodeBHist (eventAt 7 ef))
      (decodeBHist (eventAt 8 ef))
      (decodeBHist (eventAt 9 ef))
      (decodeBHist (eventAt 10 ef)))

private theorem round_trip (x : MetaCICNormalizationAuditPacketUp) :
    fromEventFlow (toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T K A S I P F H C G N =>
      change
        some
          (MetaCICNormalizationAuditPacketUp.mk
            (decodeBHist (encodeBHist T))
            (decodeBHist (encodeBHist K))
            (decodeBHist (encodeBHist A))
            (decodeBHist (encodeBHist S))
            (decodeBHist (encodeBHist I))
            (decodeBHist (encodeBHist P))
            (decodeBHist (encodeBHist F))
            (decodeBHist (encodeBHist H))
            (decodeBHist (encodeBHist C))
            (decodeBHist (encodeBHist G))
            (decodeBHist (encodeBHist N))) =
          some (MetaCICNormalizationAuditPacketUp.mk T K A S I P F H C G N)
      rw [decode_encode T, decode_encode K, decode_encode A, decode_encode S,
        decode_encode I, decode_encode P, decode_encode F, decode_encode H,
        decode_encode C, decode_encode G, decode_encode N]

private theorem toEventFlow_injective {x y : MetaCICNormalizationAuditPacketUp} :
    toEventFlow x = toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : fromEventFlow (toEventFlow x) = fromEventFlow (toEventFlow y) :=
    congrArg fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (round_trip x).symm (Eq.trans hread (round_trip y)))

private theorem fields_faithful :
    forall x y : MetaCICNormalizationAuditPacketUp, fields x = fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 K1 A1 S1 I1 P1 F1 H1 C1 G1 N1 =>
      cases y with
      | mk T2 K2 A2 S2 I2 P2 F2 H2 C2 G2 N2 =>
          cases hfields
          rfl

instance metaCICNormalizationAuditPacketBHistCarrier :
    BHistCarrier MetaCICNormalizationAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := toEventFlow
  fromEventFlow := fromEventFlow

instance metaCICNormalizationAuditPacketChapterTasteGate :
    ChapterTasteGate MetaCICNormalizationAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fromEventFlow (toEventFlow x) = some x
    exact round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (toEventFlow_injective heq)

instance metaCICNormalizationAuditPacketFieldFaithful :
    FieldFaithful MetaCICNormalizationAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fields
  field_faithful := fields_faithful

instance metaCICNormalizationAuditPacketNontrivial :
    Nontrivial MetaCICNormalizationAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICNormalizationAuditPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICNormalizationAuditPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

end BEDC.Derived.MetaCICNormalizationAuditPacketUp
