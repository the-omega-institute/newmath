import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DilworthDecompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DilworthDecompositionUp : Type where
  | mk (O A K M F H C P N : BHist) : DilworthDecompositionUp
  deriving DecidableEq

def dilworthDecompositionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dilworthDecompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dilworthDecompositionEncodeBHist h

def dilworthDecompositionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dilworthDecompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dilworthDecompositionDecodeBHist tail)

private theorem DilworthDecompositionTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dilworthDecompositionFields : DilworthDecompositionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DilworthDecompositionUp.mk O A K M F H C P N => [O, A, K, M, F, H, C, P, N]

def dilworthDecompositionToEventFlow : DilworthDecompositionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map dilworthDecompositionEncodeBHist (dilworthDecompositionFields x)

private def dilworthDecompositionEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dilworthDecompositionEventAt index rest

def dilworthDecompositionFromEventFlow : EventFlow -> Option DilworthDecompositionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DilworthDecompositionUp.mk
          (dilworthDecompositionDecodeBHist (dilworthDecompositionEventAt 0 ef))
          (dilworthDecompositionDecodeBHist (dilworthDecompositionEventAt 1 ef))
          (dilworthDecompositionDecodeBHist (dilworthDecompositionEventAt 2 ef))
          (dilworthDecompositionDecodeBHist (dilworthDecompositionEventAt 3 ef))
          (dilworthDecompositionDecodeBHist (dilworthDecompositionEventAt 4 ef))
          (dilworthDecompositionDecodeBHist (dilworthDecompositionEventAt 5 ef))
          (dilworthDecompositionDecodeBHist (dilworthDecompositionEventAt 6 ef))
          (dilworthDecompositionDecodeBHist (dilworthDecompositionEventAt 7 ef))
          (dilworthDecompositionDecodeBHist (dilworthDecompositionEventAt 8 ef)))

private theorem DilworthDecompositionTasteGate_single_carrier_alignment_round_trip :
    forall x : DilworthDecompositionUp,
      dilworthDecompositionFromEventFlow (dilworthDecompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O A K M F H C P N =>
      change
        some
            (DilworthDecompositionUp.mk
              (dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist O))
              (dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist A))
              (dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist K))
              (dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist M))
              (dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist F))
              (dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist H))
              (dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist C))
              (dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist P))
              (dilworthDecompositionDecodeBHist (dilworthDecompositionEncodeBHist N))) =
          some (DilworthDecompositionUp.mk O A K M F H C P N)
      rw [DilworthDecompositionTasteGate_single_carrier_alignment_decode O,
        DilworthDecompositionTasteGate_single_carrier_alignment_decode A,
        DilworthDecompositionTasteGate_single_carrier_alignment_decode K,
        DilworthDecompositionTasteGate_single_carrier_alignment_decode M,
        DilworthDecompositionTasteGate_single_carrier_alignment_decode F,
        DilworthDecompositionTasteGate_single_carrier_alignment_decode H,
        DilworthDecompositionTasteGate_single_carrier_alignment_decode C,
        DilworthDecompositionTasteGate_single_carrier_alignment_decode P,
        DilworthDecompositionTasteGate_single_carrier_alignment_decode N]

private theorem DilworthDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DilworthDecompositionUp} :
    dilworthDecompositionToEventFlow x = dilworthDecompositionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dilworthDecompositionFromEventFlow (dilworthDecompositionToEventFlow x) =
        dilworthDecompositionFromEventFlow (dilworthDecompositionToEventFlow y) :=
    congrArg dilworthDecompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DilworthDecompositionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DilworthDecompositionTasteGate_single_carrier_alignment_round_trip y)))

instance dilworthDecompositionBHistCarrier : BHistCarrier DilworthDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dilworthDecompositionToEventFlow
  fromEventFlow := dilworthDecompositionFromEventFlow

instance dilworthDecompositionChapterTasteGate : ChapterTasteGate DilworthDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dilworthDecompositionFromEventFlow (dilworthDecompositionToEventFlow x) = some x
    exact DilworthDecompositionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DilworthDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def dilworthDecompositionTasteGate : ChapterTasteGate DilworthDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dilworthDecompositionChapterTasteGate

theorem DilworthDecompositionTasteGate_single_carrier_alignment :
    ChapterTasteGate DilworthDecompositionUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact dilworthDecompositionChapterTasteGate

end BEDC.Derived.DilworthDecompositionUp
