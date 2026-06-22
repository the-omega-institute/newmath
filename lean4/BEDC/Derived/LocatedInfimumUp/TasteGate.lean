import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedInfimumUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedInfimumUp : Type where
  | mk : (family lower greatest window regseq realSeal transport route provenance name : BHist) →
      LocatedInfimumUp
  deriving DecidableEq

def locatedInfimumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedInfimumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedInfimumEncodeBHist h

def locatedInfimumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedInfimumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedInfimumDecodeBHist tail)

private theorem LocatedInfimumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedInfimumDecodeBHist (locatedInfimumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedInfimumFields : LocatedInfimumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedInfimumUp.mk family lower greatest window regseq realSeal transport route
      provenance name =>
      [family, lower, greatest, window, regseq, realSeal, transport, route, provenance, name]

def locatedInfimumToEventFlow : LocatedInfimumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedInfimumFields x).map locatedInfimumEncodeBHist

private def locatedInfimumEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedInfimumEventAt index rest

def locatedInfimumFromEventFlow (ef : EventFlow) : Option LocatedInfimumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedInfimumUp.mk
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 0 ef))
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 1 ef))
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 2 ef))
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 3 ef))
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 4 ef))
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 5 ef))
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 6 ef))
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 7 ef))
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 8 ef))
      (locatedInfimumDecodeBHist (locatedInfimumEventAt 9 ef)))

private theorem LocatedInfimumTasteGate_single_carrier_alignment_round_trip
    (x : LocatedInfimumUp) :
    locatedInfimumFromEventFlow (locatedInfimumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk family lower greatest window regseq realSeal transport route provenance name =>
      change
        some
          (LocatedInfimumUp.mk
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist family))
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist lower))
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist greatest))
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist window))
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist regseq))
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist realSeal))
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist transport))
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist route))
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist provenance))
            (locatedInfimumDecodeBHist (locatedInfimumEncodeBHist name))) =
          some
            (LocatedInfimumUp.mk family lower greatest window regseq realSeal transport route
              provenance name)
      rw [LocatedInfimumTasteGate_single_carrier_alignment_decode_encode family,
        LocatedInfimumTasteGate_single_carrier_alignment_decode_encode lower,
        LocatedInfimumTasteGate_single_carrier_alignment_decode_encode greatest,
        LocatedInfimumTasteGate_single_carrier_alignment_decode_encode window,
        LocatedInfimumTasteGate_single_carrier_alignment_decode_encode regseq,
        LocatedInfimumTasteGate_single_carrier_alignment_decode_encode realSeal,
        LocatedInfimumTasteGate_single_carrier_alignment_decode_encode transport,
        LocatedInfimumTasteGate_single_carrier_alignment_decode_encode route,
        LocatedInfimumTasteGate_single_carrier_alignment_decode_encode provenance,
        LocatedInfimumTasteGate_single_carrier_alignment_decode_encode name]

private theorem LocatedInfimumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedInfimumUp} :
    locatedInfimumToEventFlow x = locatedInfimumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedInfimumFromEventFlow (locatedInfimumToEventFlow x) =
        locatedInfimumFromEventFlow (locatedInfimumToEventFlow y) :=
    congrArg locatedInfimumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedInfimumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedInfimumTasteGate_single_carrier_alignment_round_trip y)))

instance locatedInfimumBHistCarrier : BHistCarrier LocatedInfimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedInfimumToEventFlow
  fromEventFlow := locatedInfimumFromEventFlow

instance locatedInfimumChapterTasteGate : ChapterTasteGate LocatedInfimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedInfimumFromEventFlow (locatedInfimumToEventFlow x) = some x
    exact LocatedInfimumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedInfimumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedInfimumTasteGate_single_carrier_alignment :
    (forall h : BHist, locatedInfimumDecodeBHist (locatedInfimumEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate LocatedInfimumUp) ∧
        locatedInfimumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedInfimumTasteGate_single_carrier_alignment_decode_encode,
      ⟨locatedInfimumChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedInfimumUp.TasteGate
