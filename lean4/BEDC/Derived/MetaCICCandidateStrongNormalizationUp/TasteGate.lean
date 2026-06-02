import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICCandidateStrongNormalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICCandidateStrongNormalizationUp : Type where
  | mk (T K F E R A H C P N G : BHist) : MetaCICCandidateStrongNormalizationUp
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

private def fields : MetaCICCandidateStrongNormalizationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICCandidateStrongNormalizationUp.mk T K F E R A H C P N G =>
      [T, K, F, E, R, A, H, C, P, N, G]

private def toEventFlow : MetaCICCandidateStrongNormalizationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fields x).map encodeBHist

private def eventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eventAt index rest

private def fromEventFlow (ef : EventFlow) :
    Option MetaCICCandidateStrongNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICCandidateStrongNormalizationUp.mk
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

private theorem round_trip (x : MetaCICCandidateStrongNormalizationUp) :
    fromEventFlow (toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T K F E R A H C P N G =>
      change
        some
          (MetaCICCandidateStrongNormalizationUp.mk
            (decodeBHist (encodeBHist T))
            (decodeBHist (encodeBHist K))
            (decodeBHist (encodeBHist F))
            (decodeBHist (encodeBHist E))
            (decodeBHist (encodeBHist R))
            (decodeBHist (encodeBHist A))
            (decodeBHist (encodeBHist H))
            (decodeBHist (encodeBHist C))
            (decodeBHist (encodeBHist P))
            (decodeBHist (encodeBHist N))
            (decodeBHist (encodeBHist G))) =
          some (MetaCICCandidateStrongNormalizationUp.mk T K F E R A H C P N G)
      rw [decode_encode T, decode_encode K, decode_encode F, decode_encode E,
        decode_encode R, decode_encode A, decode_encode H, decode_encode C,
        decode_encode P, decode_encode N, decode_encode G]

private theorem toEventFlow_injective {x y : MetaCICCandidateStrongNormalizationUp} :
    toEventFlow x = toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : fromEventFlow (toEventFlow x) = fromEventFlow (toEventFlow y) :=
    congrArg fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (round_trip x).symm (Eq.trans hread (round_trip y)))

private theorem fields_faithful :
    forall x y : MetaCICCandidateStrongNormalizationUp, fields x = fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 K1 F1 E1 R1 A1 H1 C1 P1 N1 G1 =>
      cases y with
      | mk T2 K2 F2 E2 R2 A2 H2 C2 P2 N2 G2 =>
          cases hfields
          rfl

instance metaCICCandidateStrongNormalizationBHistCarrier :
    BHistCarrier MetaCICCandidateStrongNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := toEventFlow
  fromEventFlow := fromEventFlow

instance metaCICCandidateStrongNormalizationChapterTasteGate :
    ChapterTasteGate MetaCICCandidateStrongNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fromEventFlow (toEventFlow x) = some x
    exact round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (toEventFlow_injective heq)

instance metaCICCandidateStrongNormalizationFieldFaithful :
    FieldFaithful MetaCICCandidateStrongNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fields
  field_faithful := fields_faithful

instance metaCICCandidateStrongNormalizationNontrivial :
    Nontrivial MetaCICCandidateStrongNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICCandidateStrongNormalizationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MetaCICCandidateStrongNormalizationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

end BEDC.Derived.MetaCICCandidateStrongNormalizationUp
