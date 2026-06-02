import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KSpaceUp : Type where
  | mk (X T Q A E H C P N : BHist) : KSpaceUp

def kSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kSpaceEncodeBHist h

def kSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kSpaceDecodeBHist tail)

private theorem KSpaceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, kSpaceDecodeBHist (kSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kSpaceFields : KSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KSpaceUp.mk X T Q A E H C P N => [X, T, Q, A, E, H, C, P, N]

def kSpaceToEventFlow : KSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kSpaceFields x).map kSpaceEncodeBHist

private def kSpaceEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kSpaceEventAt index rest

def kSpaceFromEventFlow (ef : EventFlow) : Option KSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KSpaceUp.mk
      (kSpaceDecodeBHist (kSpaceEventAt 0 ef))
      (kSpaceDecodeBHist (kSpaceEventAt 1 ef))
      (kSpaceDecodeBHist (kSpaceEventAt 2 ef))
      (kSpaceDecodeBHist (kSpaceEventAt 3 ef))
      (kSpaceDecodeBHist (kSpaceEventAt 4 ef))
      (kSpaceDecodeBHist (kSpaceEventAt 5 ef))
      (kSpaceDecodeBHist (kSpaceEventAt 6 ef))
      (kSpaceDecodeBHist (kSpaceEventAt 7 ef))
      (kSpaceDecodeBHist (kSpaceEventAt 8 ef)))

private theorem KSpaceTasteGate_single_carrier_alignment_round_trip (x : KSpaceUp) :
    kSpaceFromEventFlow (kSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X T Q A E H C P N =>
      change
        some
          (KSpaceUp.mk
            (kSpaceDecodeBHist (kSpaceEncodeBHist X))
            (kSpaceDecodeBHist (kSpaceEncodeBHist T))
            (kSpaceDecodeBHist (kSpaceEncodeBHist Q))
            (kSpaceDecodeBHist (kSpaceEncodeBHist A))
            (kSpaceDecodeBHist (kSpaceEncodeBHist E))
            (kSpaceDecodeBHist (kSpaceEncodeBHist H))
            (kSpaceDecodeBHist (kSpaceEncodeBHist C))
            (kSpaceDecodeBHist (kSpaceEncodeBHist P))
            (kSpaceDecodeBHist (kSpaceEncodeBHist N))) =
          some (KSpaceUp.mk X T Q A E H C P N)
      rw [KSpaceTasteGate_single_carrier_alignment_decode_encode X,
        KSpaceTasteGate_single_carrier_alignment_decode_encode T,
        KSpaceTasteGate_single_carrier_alignment_decode_encode Q,
        KSpaceTasteGate_single_carrier_alignment_decode_encode A,
        KSpaceTasteGate_single_carrier_alignment_decode_encode E,
        KSpaceTasteGate_single_carrier_alignment_decode_encode H,
        KSpaceTasteGate_single_carrier_alignment_decode_encode C,
        KSpaceTasteGate_single_carrier_alignment_decode_encode P,
        KSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem KSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KSpaceUp} :
    kSpaceToEventFlow x = kSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kSpaceFromEventFlow (kSpaceToEventFlow x) =
        kSpaceFromEventFlow (kSpaceToEventFlow y) :=
    congrArg kSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance kSpaceBHistCarrier : BHistCarrier KSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kSpaceToEventFlow
  fromEventFlow := kSpaceFromEventFlow

instance kSpaceChapterTasteGate : ChapterTasteGate KSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kSpaceFromEventFlow (kSpaceToEventFlow x) = some x
    exact KSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem KSpaceTasteGate_single_carrier_alignment :
    (forall h : BHist, kSpaceDecodeBHist (kSpaceEncodeBHist h) = h) /\
      Nonempty (BHistCarrier KSpaceUp) /\
        Nonempty (ChapterTasteGate KSpaceUp) /\
          kSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨kSpaceBHistCarrier⟩,
      ⟨kSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.KSpaceUp
