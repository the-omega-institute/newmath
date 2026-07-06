import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StrongChoquetSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StrongChoquetSpaceUp : Type where
  | mk (T B O R S W H C P N : BHist) : StrongChoquetSpaceUp
  deriving DecidableEq

private def StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist h

private def StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def StrongChoquetSpaceTasteGate_single_carrier_alignment_fields :
    StrongChoquetSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StrongChoquetSpaceUp.mk T B O R S W H C P N => [T, B, O, R, S, W, H, C, P, N]

private def StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow :
    StrongChoquetSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_fields x).map
        StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist

private def StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt index rest

private def StrongChoquetSpaceTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option StrongChoquetSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StrongChoquetSpaceUp.mk
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 0 ef))
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 1 ef))
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 2 ef))
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 3 ef))
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 4 ef))
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 5 ef))
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 6 ef))
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 7 ef))
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 8 ef))
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem StrongChoquetSpaceTasteGate_single_carrier_alignment_round_trip
    (x : StrongChoquetSpaceUp) :
    StrongChoquetSpaceTasteGate_single_carrier_alignment_fromEventFlow
      (StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T B O R S W H C P N =>
      change
        some
          (StrongChoquetSpaceUp.mk
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist T))
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist B))
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist O))
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist R))
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist S))
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist W))
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist H))
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist C))
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist P))
            (StrongChoquetSpaceTasteGate_single_carrier_alignment_decodeBHist
              (StrongChoquetSpaceTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (StrongChoquetSpaceUp.mk T B O R S W H C P N)
      rw [StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode T,
        StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode B,
        StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode O,
        StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode R,
        StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode S,
        StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode W,
        StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode H,
        StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode C,
        StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode P,
        StrongChoquetSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StrongChoquetSpaceUp} :
    StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow x =
      StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      StrongChoquetSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow x) =
        StrongChoquetSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg StrongChoquetSpaceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StrongChoquetSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StrongChoquetSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance strongChoquetSpaceBHistCarrier : BHistCarrier StrongChoquetSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := StrongChoquetSpaceTasteGate_single_carrier_alignment_fromEventFlow

instance strongChoquetSpaceChapterTasteGate :
    ChapterTasteGate StrongChoquetSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      StrongChoquetSpaceTasteGate_single_carrier_alignment_fromEventFlow
        (StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact StrongChoquetSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StrongChoquetSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem StrongChoquetSpaceTasteGate_single_carrier_alignment :
    Nonempty StrongChoquetSpaceUp ∧
      ∃ carrierInst : BHistCarrier StrongChoquetSpaceUp,
        @ChapterTasteGate StrongChoquetSpaceUp carrierInst := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨StrongChoquetSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty
    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty⟩,
    ⟨strongChoquetSpaceBHistCarrier, strongChoquetSpaceChapterTasteGate⟩⟩

end BEDC.Derived.StrongChoquetSpaceUp.TasteGate
