import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedIntervalTotalBoundedUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedIntervalTotalBoundedUp : Type where
  | mk (lower upper mesh dyadicRefinement finiteNet totalBounded window readback realSeal
      transport replay provenance localName : BHist) : ClosedIntervalTotalBoundedUp

def closedIntervalTotalBoundedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedIntervalTotalBoundedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedIntervalTotalBoundedEncodeBHist h

def closedIntervalTotalBoundedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedIntervalTotalBoundedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedIntervalTotalBoundedDecodeBHist tail)

private theorem ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedIntervalTotalBoundedFields : ClosedIntervalTotalBoundedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalTotalBoundedUp.mk lower upper mesh dyadicRefinement finiteNet totalBounded
      window readback realSeal transport replay provenance localName =>
      [lower, upper, mesh, dyadicRefinement, finiteNet, totalBounded, window, readback,
        realSeal, transport, replay, provenance, localName]

def closedIntervalTotalBoundedToEventFlow : ClosedIntervalTotalBoundedUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (closedIntervalTotalBoundedFields x).map closedIntervalTotalBoundedEncodeBHist

private def closedIntervalTotalBoundedEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedIntervalTotalBoundedEventAtDefault index rest

def closedIntervalTotalBoundedFromEventFlow
    (ef : EventFlow) : Option ClosedIntervalTotalBoundedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedIntervalTotalBoundedUp.mk
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 0 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 1 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 2 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 3 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 4 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 5 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 6 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 7 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 8 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 9 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 10 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 11 ef))
      (closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEventAtDefault 12 ef)))

private theorem ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedIntervalTotalBoundedUp,
      closedIntervalTotalBoundedFromEventFlow
          (closedIntervalTotalBoundedToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lower upper mesh dyadicRefinement finiteNet totalBounded window readback realSeal
      transport replay provenance localName =>
      change
        some
          (ClosedIntervalTotalBoundedUp.mk
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist lower))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist upper))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist mesh))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist dyadicRefinement))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist finiteNet))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist totalBounded))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist window))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist readback))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist realSeal))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist transport))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist replay))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist provenance))
            (closedIntervalTotalBoundedDecodeBHist
              (closedIntervalTotalBoundedEncodeBHist localName))) =
          some
            (ClosedIntervalTotalBoundedUp.mk lower upper mesh dyadicRefinement finiteNet
              totalBounded window readback realSeal transport replay provenance localName)
      rw [ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode lower,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode upper,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode mesh,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode dyadicRefinement,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode finiteNet,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode totalBounded,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode window,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode readback,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode realSeal,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode transport,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode replay,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode provenance,
        ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode localName]

private theorem ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedIntervalTotalBoundedUp} :
    closedIntervalTotalBoundedToEventFlow x = closedIntervalTotalBoundedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalTotalBoundedFromEventFlow (closedIntervalTotalBoundedToEventFlow x) =
        closedIntervalTotalBoundedFromEventFlow (closedIntervalTotalBoundedToEventFlow y) :=
    congrArg closedIntervalTotalBoundedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_round_trip y)))

instance closedIntervalTotalBoundedBHistCarrier :
    BHistCarrier ClosedIntervalTotalBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedIntervalTotalBoundedToEventFlow
  fromEventFlow := closedIntervalTotalBoundedFromEventFlow

instance closedIntervalTotalBoundedChapterTasteGate :
    ChapterTasteGate ClosedIntervalTotalBoundedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedIntervalTotalBoundedFromEventFlow (closedIntervalTotalBoundedToEventFlow x) =
        some x
    exact ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ClosedIntervalTotalBoundedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedIntervalTotalBoundedChapterTasteGate

theorem ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ClosedIntervalTotalBoundedUp) ∧
      (∀ h : BHist,
        closedIntervalTotalBoundedDecodeBHist (closedIntervalTotalBoundedEncodeBHist h) = h) ∧
        (∀ x : ClosedIntervalTotalBoundedUp,
          closedIntervalTotalBoundedFromEventFlow
              (closedIntervalTotalBoundedToEventFlow x) =
            some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨closedIntervalTotalBoundedChapterTasteGate⟩,
      ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_decode_encode,
      ClosedIntervalTotalBoundedTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.ClosedIntervalTotalBoundedUp
