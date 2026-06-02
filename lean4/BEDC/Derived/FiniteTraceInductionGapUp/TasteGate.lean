import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteTraceInductionGapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteTraceInductionGapUp : Type where
  | mk (trace observed attempted gap transport replay provenance localName : BHist) :
      FiniteTraceInductionGapUp
  deriving DecidableEq

def finiteTraceInductionGapEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteTraceInductionGapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteTraceInductionGapEncodeBHist h

def finiteTraceInductionGapDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteTraceInductionGapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteTraceInductionGapDecodeBHist tail)

private theorem FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteTraceInductionGapFields : FiniteTraceInductionGapUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteTraceInductionGapUp.mk trace observed attempted gap transport replay provenance
      localName =>
      [trace, observed, attempted, gap, transport, replay, provenance, localName]

def finiteTraceInductionGapToEventFlow : FiniteTraceInductionGapUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteTraceInductionGapFields x).map finiteTraceInductionGapEncodeBHist

private def finiteTraceInductionGapEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteTraceInductionGapEventAtDefault index rest

def finiteTraceInductionGapFromEventFlow
    (ef : EventFlow) : Option FiniteTraceInductionGapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteTraceInductionGapUp.mk
      (finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEventAtDefault 0 ef))
      (finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEventAtDefault 1 ef))
      (finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEventAtDefault 2 ef))
      (finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEventAtDefault 3 ef))
      (finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEventAtDefault 4 ef))
      (finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEventAtDefault 5 ef))
      (finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEventAtDefault 6 ef))
      (finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEventAtDefault 7 ef)))

private theorem FiniteTraceInductionGapTasteGate_single_carrier_alignment_round_trip :
    forall x : FiniteTraceInductionGapUp,
      finiteTraceInductionGapFromEventFlow (finiteTraceInductionGapToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk trace observed attempted gap transport replay provenance localName =>
      change
        some
          (FiniteTraceInductionGapUp.mk
            (finiteTraceInductionGapDecodeBHist
              (finiteTraceInductionGapEncodeBHist trace))
            (finiteTraceInductionGapDecodeBHist
              (finiteTraceInductionGapEncodeBHist observed))
            (finiteTraceInductionGapDecodeBHist
              (finiteTraceInductionGapEncodeBHist attempted))
            (finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEncodeBHist gap))
            (finiteTraceInductionGapDecodeBHist
              (finiteTraceInductionGapEncodeBHist transport))
            (finiteTraceInductionGapDecodeBHist
              (finiteTraceInductionGapEncodeBHist replay))
            (finiteTraceInductionGapDecodeBHist
              (finiteTraceInductionGapEncodeBHist provenance))
            (finiteTraceInductionGapDecodeBHist
              (finiteTraceInductionGapEncodeBHist localName))) =
          some
            (FiniteTraceInductionGapUp.mk trace observed attempted gap transport replay
              provenance localName)
      rw [FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode trace,
        FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode observed,
        FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode attempted,
        FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode gap,
        FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode transport,
        FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode replay,
        FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode provenance,
        FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode localName]

private theorem FiniteTraceInductionGapTasteGate_single_carrier_alignment_injective
    {x y : FiniteTraceInductionGapUp} :
    finiteTraceInductionGapToEventFlow x = finiteTraceInductionGapToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteTraceInductionGapFromEventFlow (finiteTraceInductionGapToEventFlow x) =
        finiteTraceInductionGapFromEventFlow (finiteTraceInductionGapToEventFlow y) :=
    congrArg finiteTraceInductionGapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteTraceInductionGapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteTraceInductionGapTasteGate_single_carrier_alignment_round_trip y)))

instance finiteTraceInductionGapBHistCarrier : BHistCarrier FiniteTraceInductionGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteTraceInductionGapToEventFlow
  fromEventFlow := finiteTraceInductionGapFromEventFlow

instance finiteTraceInductionGapChapterTasteGate :
    ChapterTasteGate FiniteTraceInductionGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteTraceInductionGapFromEventFlow (finiteTraceInductionGapToEventFlow x) =
        some x
    exact FiniteTraceInductionGapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteTraceInductionGapTasteGate_single_carrier_alignment_injective heq)

theorem FiniteTraceInductionGapTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FiniteTraceInductionGapUp) ∧
      Nonempty (ChapterTasteGate FiniteTraceInductionGapUp) ∧
        (forall h : BHist,
          finiteTraceInductionGapDecodeBHist (finiteTraceInductionGapEncodeBHist h) = h) ∧
          (forall x : FiniteTraceInductionGapUp,
            finiteTraceInductionGapFromEventFlow (finiteTraceInductionGapToEventFlow x) =
              some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨finiteTraceInductionGapBHistCarrier⟩,
      ⟨finiteTraceInductionGapChapterTasteGate⟩,
      FiniteTraceInductionGapTasteGate_single_carrier_alignment_decode,
      FiniteTraceInductionGapTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.FiniteTraceInductionGapUp
