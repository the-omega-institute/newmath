import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformModulusExtractorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformModulusExtractorUp : Type where
  | mk (K F T P L M U H C G N : BHist) : CompactUniformModulusExtractorUp
  deriving DecidableEq

private def compactUniformModulusExtractorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformModulusExtractorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformModulusExtractorEncodeBHist h

private def compactUniformModulusExtractorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformModulusExtractorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformModulusExtractorDecodeBHist tail)

private theorem CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def compactUniformModulusExtractorFields :
    CompactUniformModulusExtractorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformModulusExtractorUp.mk K F T P L M U H C G N =>
      [K, F, T, P, L, M, U, H, C, G, N]

private def compactUniformModulusExtractorToEventFlow :
    CompactUniformModulusExtractorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformModulusExtractorFields x).map compactUniformModulusExtractorEncodeBHist

private def compactUniformModulusExtractorEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformModulusExtractorEventAt index rest

private def compactUniformModulusExtractorFromEventFlow (ef : EventFlow) :
    Option CompactUniformModulusExtractorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformModulusExtractorUp.mk
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 0 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 1 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 2 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 3 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 4 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 5 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 6 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 7 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 8 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 9 ef))
      (compactUniformModulusExtractorDecodeBHist
        (compactUniformModulusExtractorEventAt 10 ef)))

private theorem CompactUniformModulusExtractorTasteGate_single_carrier_alignment_round_trip
    (x : CompactUniformModulusExtractorUp) :
    compactUniformModulusExtractorFromEventFlow
      (compactUniformModulusExtractorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F T P L M U H C G N =>
      change
        some
          (CompactUniformModulusExtractorUp.mk
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist K))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist F))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist T))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist P))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist L))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist M))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist U))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist H))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist C))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist G))
            (compactUniformModulusExtractorDecodeBHist
              (compactUniformModulusExtractorEncodeBHist N))) =
          some (CompactUniformModulusExtractorUp.mk K F T P L M U H C G N)
      rw [CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode K,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode F,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode T,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode P,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode L,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode M,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode U,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode H,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode C,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode G,
        CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode N]

private theorem
    CompactUniformModulusExtractorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformModulusExtractorUp} :
    compactUniformModulusExtractorToEventFlow x =
      compactUniformModulusExtractorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformModulusExtractorFromEventFlow
        (compactUniformModulusExtractorToEventFlow x) =
        compactUniformModulusExtractorFromEventFlow
          (compactUniformModulusExtractorToEventFlow y) :=
    congrArg compactUniformModulusExtractorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformModulusExtractorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformModulusExtractorTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformModulusExtractorBHistCarrier :
    BHistCarrier CompactUniformModulusExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformModulusExtractorToEventFlow
  fromEventFlow := compactUniformModulusExtractorFromEventFlow

instance compactUniformModulusExtractorChapterTasteGate :
    ChapterTasteGate CompactUniformModulusExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactUniformModulusExtractorFromEventFlow
      (compactUniformModulusExtractorToEventFlow x) = some x
    exact CompactUniformModulusExtractorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformModulusExtractorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactUniformModulusExtractorTasteGate_single_carrier_alignment :
    (forall h : BHist,
        compactUniformModulusExtractorDecodeBHist
          (compactUniformModulusExtractorEncodeBHist h) = h) ∧
      (forall x : CompactUniformModulusExtractorUp,
        compactUniformModulusExtractorFromEventFlow
          (compactUniformModulusExtractorToEventFlow x) = some x) ∧
        (forall x y : CompactUniformModulusExtractorUp,
          compactUniformModulusExtractorToEventFlow x =
            compactUniformModulusExtractorToEventFlow y -> x = y) ∧
          compactUniformModulusExtractorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CompactUniformModulusExtractorTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CompactUniformModulusExtractorTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          CompactUniformModulusExtractorTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CompactUniformModulusExtractorUp
