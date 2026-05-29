import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformModulusStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformModulusStabilityUp : Type where
  | mk (K N M F U T H C P L : BHist) : CompactUniformModulusStabilityUp
  deriving DecidableEq

private def compactUniformModulusStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformModulusStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformModulusStabilityEncodeBHist h

private def compactUniformModulusStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformModulusStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformModulusStabilityDecodeBHist tail)

private theorem CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def compactUniformModulusStabilityFields :
    CompactUniformModulusStabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformModulusStabilityUp.mk K N M F U T H C P L =>
      [K, N, M, F, U, T, H, C, P, L]

private def compactUniformModulusStabilityToEventFlow :
    CompactUniformModulusStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformModulusStabilityFields x).map
      compactUniformModulusStabilityEncodeBHist

private def compactUniformModulusStabilityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformModulusStabilityEventAt index rest

private def compactUniformModulusStabilityFromEventFlow
    (ef : EventFlow) : Option CompactUniformModulusStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformModulusStabilityUp.mk
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 0 ef))
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 1 ef))
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 2 ef))
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 3 ef))
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 4 ef))
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 5 ef))
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 6 ef))
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 7 ef))
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 8 ef))
      (compactUniformModulusStabilityDecodeBHist
        (compactUniformModulusStabilityEventAt 9 ef)))

private theorem CompactUniformModulusStabilityTasteGate_single_carrier_alignment_round_trip
    (x : CompactUniformModulusStabilityUp) :
    compactUniformModulusStabilityFromEventFlow
        (compactUniformModulusStabilityToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K N M F U T H C P L =>
      change
        some
          (CompactUniformModulusStabilityUp.mk
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist K))
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist N))
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist M))
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist F))
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist U))
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist T))
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist H))
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist C))
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist P))
            (compactUniformModulusStabilityDecodeBHist
              (compactUniformModulusStabilityEncodeBHist L))) =
          some (CompactUniformModulusStabilityUp.mk K N M F U T H C P L)
      rw [CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode K,
        CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode N,
        CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode M,
        CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode F,
        CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode U,
        CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode T,
        CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode H,
        CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode C,
        CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode P,
        CompactUniformModulusStabilityTasteGate_single_carrier_alignment_decode_encode L]

private theorem CompactUniformModulusStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformModulusStabilityUp} :
    compactUniformModulusStabilityToEventFlow x =
        compactUniformModulusStabilityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformModulusStabilityFromEventFlow
          (compactUniformModulusStabilityToEventFlow x) =
        compactUniformModulusStabilityFromEventFlow
          (compactUniformModulusStabilityToEventFlow y) :=
    congrArg compactUniformModulusStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformModulusStabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformModulusStabilityTasteGate_single_carrier_alignment_round_trip y)))

instance compactUniformModulusStabilityBHistCarrier :
    BHistCarrier CompactUniformModulusStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformModulusStabilityToEventFlow
  fromEventFlow := compactUniformModulusStabilityFromEventFlow

instance compactUniformModulusStabilityChapterTasteGate :
    ChapterTasteGate CompactUniformModulusStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactUniformModulusStabilityFromEventFlow
      (compactUniformModulusStabilityToEventFlow x) = some x
    exact CompactUniformModulusStabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformModulusStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem CompactUniformModulusStabilityTasteGate_single_carrier_alignment :
    ChapterTasteGate CompactUniformModulusStabilityUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact compactUniformModulusStabilityChapterTasteGate

end BEDC.Derived.CompactUniformModulusStabilityUp
