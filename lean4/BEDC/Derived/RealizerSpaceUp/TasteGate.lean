import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealizerSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealizerSpaceUp : Type where
  | mk (X A K W Q D E F H C P N : BHist) : RealizerSpaceUp
  deriving DecidableEq

private def realizerSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realizerSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realizerSpaceEncodeBHist h

private def realizerSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realizerSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realizerSpaceDecodeBHist tail)

private theorem RealizerSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realizerSpaceDecodeBHist (realizerSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def realizerSpaceFields : RealizerSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealizerSpaceUp.mk X A K W Q D E F H C P N =>
      [X, A, K, W, Q, D, E, F, H, C, P, N]

private def realizerSpaceToEventFlow : RealizerSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realizerSpaceFields x).map realizerSpaceEncodeBHist

private def realizerSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realizerSpaceEventAt index rest

private def realizerSpaceFromEventFlow
    (ef : EventFlow) : Option RealizerSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealizerSpaceUp.mk
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 0 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 1 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 2 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 3 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 4 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 5 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 6 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 7 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 8 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 9 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 10 ef))
      (realizerSpaceDecodeBHist (realizerSpaceEventAt 11 ef)))

private theorem RealizerSpaceTasteGate_single_carrier_alignment_round_trip
    (x : RealizerSpaceUp) :
    realizerSpaceFromEventFlow (realizerSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X A K W Q D E F H C P N =>
      change
        some
          (RealizerSpaceUp.mk
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist X))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist A))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist K))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist W))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist Q))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist D))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist E))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist F))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist H))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist C))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist P))
            (realizerSpaceDecodeBHist (realizerSpaceEncodeBHist N))) =
          some (RealizerSpaceUp.mk X A K W Q D E F H C P N)
      rw [RealizerSpaceTasteGate_single_carrier_alignment_decode_encode X,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode A,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode K,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode W,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode Q,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode D,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode E,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode F,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode H,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode C,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode P,
        RealizerSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealizerSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealizerSpaceUp} :
    realizerSpaceToEventFlow x = realizerSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realizerSpaceFromEventFlow (realizerSpaceToEventFlow x) =
        realizerSpaceFromEventFlow (realizerSpaceToEventFlow y) :=
    congrArg realizerSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealizerSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealizerSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance realizerSpaceBHistCarrier : BHistCarrier RealizerSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realizerSpaceToEventFlow
  fromEventFlow := realizerSpaceFromEventFlow

instance realizerSpaceChapterTasteGate :
    ChapterTasteGate RealizerSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realizerSpaceFromEventFlow (realizerSpaceToEventFlow x) = some x
    exact RealizerSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealizerSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RealizerSpaceTasteGate_single_carrier_alignment :
    ChapterTasteGate RealizerSpaceUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact realizerSpaceChapterTasteGate

end BEDC.Derived.RealizerSpaceUp
