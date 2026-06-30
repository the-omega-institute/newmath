import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactCoverNerveUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactCoverNerveUp : Type where
  | mk (K U O R F H P N : BHist) : CompactCoverNerveUp
  deriving DecidableEq

def compactCoverNerveEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactCoverNerveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactCoverNerveEncodeBHist h

private def compactCoverNerveDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactCoverNerveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactCoverNerveDecodeBHist tail)

private theorem CompactCoverNerveTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      compactCoverNerveDecodeBHist (compactCoverNerveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def compactCoverNerveFields : CompactCoverNerveUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactCoverNerveUp.mk K U O R F H P N => [K, U, O, R, F, H, P, N]

private def compactCoverNerveToEventFlow : CompactCoverNerveUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactCoverNerveFields x).map compactCoverNerveEncodeBHist

private def compactCoverNerveRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactCoverNerveRawAt index rest

private def compactCoverNerveFromEventFlow (flow : EventFlow) :
    Option CompactCoverNerveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactCoverNerveUp.mk
      (compactCoverNerveDecodeBHist (compactCoverNerveRawAt 0 flow))
      (compactCoverNerveDecodeBHist (compactCoverNerveRawAt 1 flow))
      (compactCoverNerveDecodeBHist (compactCoverNerveRawAt 2 flow))
      (compactCoverNerveDecodeBHist (compactCoverNerveRawAt 3 flow))
      (compactCoverNerveDecodeBHist (compactCoverNerveRawAt 4 flow))
      (compactCoverNerveDecodeBHist (compactCoverNerveRawAt 5 flow))
      (compactCoverNerveDecodeBHist (compactCoverNerveRawAt 6 flow))
      (compactCoverNerveDecodeBHist (compactCoverNerveRawAt 7 flow)))

private theorem CompactCoverNerveTasteGate_single_carrier_alignment_round_trip :
    forall x : CompactCoverNerveUp,
      compactCoverNerveFromEventFlow (compactCoverNerveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K U O R F H P N =>
      change
        some
          (CompactCoverNerveUp.mk
            (compactCoverNerveDecodeBHist (compactCoverNerveEncodeBHist K))
            (compactCoverNerveDecodeBHist (compactCoverNerveEncodeBHist U))
            (compactCoverNerveDecodeBHist (compactCoverNerveEncodeBHist O))
            (compactCoverNerveDecodeBHist (compactCoverNerveEncodeBHist R))
            (compactCoverNerveDecodeBHist (compactCoverNerveEncodeBHist F))
            (compactCoverNerveDecodeBHist (compactCoverNerveEncodeBHist H))
            (compactCoverNerveDecodeBHist (compactCoverNerveEncodeBHist P))
            (compactCoverNerveDecodeBHist (compactCoverNerveEncodeBHist N))) =
          some (CompactCoverNerveUp.mk K U O R F H P N)
      rw [CompactCoverNerveTasteGate_single_carrier_alignment_decode_encode K,
        CompactCoverNerveTasteGate_single_carrier_alignment_decode_encode U,
        CompactCoverNerveTasteGate_single_carrier_alignment_decode_encode O,
        CompactCoverNerveTasteGate_single_carrier_alignment_decode_encode R,
        CompactCoverNerveTasteGate_single_carrier_alignment_decode_encode F,
        CompactCoverNerveTasteGate_single_carrier_alignment_decode_encode H,
        CompactCoverNerveTasteGate_single_carrier_alignment_decode_encode P,
        CompactCoverNerveTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactCoverNerveTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactCoverNerveUp} :
    compactCoverNerveToEventFlow x = compactCoverNerveToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactCoverNerveFromEventFlow (compactCoverNerveToEventFlow x) =
        compactCoverNerveFromEventFlow (compactCoverNerveToEventFlow y) :=
    congrArg compactCoverNerveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactCoverNerveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactCoverNerveTasteGate_single_carrier_alignment_round_trip y)))

instance compactCoverNerveBHistCarrier : BHistCarrier CompactCoverNerveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactCoverNerveToEventFlow
  fromEventFlow := compactCoverNerveFromEventFlow

instance compactCoverNerveChapterTasteGate :
    ChapterTasteGate CompactCoverNerveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactCoverNerveFromEventFlow (compactCoverNerveToEventFlow x) = some x
    exact CompactCoverNerveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactCoverNerveTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactCoverNerveTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompactCoverNerveUp) ∧
      Nonempty (ChapterTasteGate CompactCoverNerveUp) ∧
        compactCoverNerveEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨compactCoverNerveBHistCarrier⟩,
      ⟨compactCoverNerveChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompactCoverNerveUp.TasteGate
