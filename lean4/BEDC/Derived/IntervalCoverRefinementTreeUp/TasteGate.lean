import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalCoverRefinementTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalCoverRefinementTreeUp : Type where
  | mk
      (rootInterval coverLedger overlapWitness refinementNode splitNode branchLeft branchRight
        meshBound compactWitness inclusionRoute localChoice treePath terminalSeal : BHist) :
      IntervalCoverRefinementTreeUp

def intervalCoverRefinementTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalCoverRefinementTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalCoverRefinementTreeEncodeBHist h

def intervalCoverRefinementTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalCoverRefinementTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalCoverRefinementTreeDecodeBHist tail)

private theorem intervalCoverRefinementTreeDecode_encode_bhist :
    ∀ h : BHist,
      intervalCoverRefinementTreeDecodeBHist
          (intervalCoverRefinementTreeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalCoverRefinementTreeFields :
    IntervalCoverRefinementTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalCoverRefinementTreeUp.mk rootInterval coverLedger overlapWitness
      refinementNode splitNode branchLeft branchRight meshBound compactWitness
      inclusionRoute localChoice treePath terminalSeal =>
      [rootInterval, coverLedger, overlapWitness, refinementNode, splitNode, branchLeft,
        branchRight, meshBound, compactWitness, inclusionRoute, localChoice, treePath,
        terminalSeal]

def intervalCoverRefinementTreeToEventFlow :
    IntervalCoverRefinementTreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (intervalCoverRefinementTreeFields x).map
      intervalCoverRefinementTreeEncodeBHist

private def intervalCoverRefinementTreeEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      intervalCoverRefinementTreeEventAtDefault index rest

def intervalCoverRefinementTreeFromEventFlow
    (ef : EventFlow) : Option IntervalCoverRefinementTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalCoverRefinementTreeUp.mk
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 0 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 1 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 2 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 3 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 4 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 5 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 6 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 7 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 8 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 9 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 10 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 11 ef))
      (intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEventAtDefault 12 ef)))

private theorem intervalCoverRefinementTree_round_trip
    (x : IntervalCoverRefinementTreeUp) :
    intervalCoverRefinementTreeFromEventFlow
        (intervalCoverRefinementTreeToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk rootInterval coverLedger overlapWitness refinementNode splitNode branchLeft
      branchRight meshBound compactWitness inclusionRoute localChoice treePath
      terminalSeal =>
      change
        some
          (IntervalCoverRefinementTreeUp.mk
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist rootInterval))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist coverLedger))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist overlapWitness))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist refinementNode))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist splitNode))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist branchLeft))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist branchRight))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist meshBound))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist compactWitness))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist inclusionRoute))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist localChoice))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist treePath))
            (intervalCoverRefinementTreeDecodeBHist
              (intervalCoverRefinementTreeEncodeBHist terminalSeal))) =
          some
            (IntervalCoverRefinementTreeUp.mk rootInterval coverLedger overlapWitness
              refinementNode splitNode branchLeft branchRight meshBound compactWitness
              inclusionRoute localChoice treePath terminalSeal)
      rw [intervalCoverRefinementTreeDecode_encode_bhist rootInterval,
        intervalCoverRefinementTreeDecode_encode_bhist coverLedger,
        intervalCoverRefinementTreeDecode_encode_bhist overlapWitness,
        intervalCoverRefinementTreeDecode_encode_bhist refinementNode,
        intervalCoverRefinementTreeDecode_encode_bhist splitNode,
        intervalCoverRefinementTreeDecode_encode_bhist branchLeft,
        intervalCoverRefinementTreeDecode_encode_bhist branchRight,
        intervalCoverRefinementTreeDecode_encode_bhist meshBound,
        intervalCoverRefinementTreeDecode_encode_bhist compactWitness,
        intervalCoverRefinementTreeDecode_encode_bhist inclusionRoute,
        intervalCoverRefinementTreeDecode_encode_bhist localChoice,
        intervalCoverRefinementTreeDecode_encode_bhist treePath,
        intervalCoverRefinementTreeDecode_encode_bhist terminalSeal]

private theorem intervalCoverRefinementTreeToEventFlow_injective
    {x y : IntervalCoverRefinementTreeUp} :
    intervalCoverRefinementTreeToEventFlow x =
      intervalCoverRefinementTreeToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalCoverRefinementTreeFromEventFlow
          (intervalCoverRefinementTreeToEventFlow x) =
        intervalCoverRefinementTreeFromEventFlow
          (intervalCoverRefinementTreeToEventFlow y) :=
    congrArg intervalCoverRefinementTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (intervalCoverRefinementTree_round_trip x).symm
      (Eq.trans hread (intervalCoverRefinementTree_round_trip y)))

instance intervalCoverRefinementTreeBHistCarrier :
    BHistCarrier IntervalCoverRefinementTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalCoverRefinementTreeToEventFlow
  fromEventFlow := intervalCoverRefinementTreeFromEventFlow

instance intervalCoverRefinementTreeChapterTasteGate :
    ChapterTasteGate IntervalCoverRefinementTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      intervalCoverRefinementTreeFromEventFlow
          (intervalCoverRefinementTreeToEventFlow x) =
        some x
    exact intervalCoverRefinementTree_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (intervalCoverRefinementTreeToEventFlow_injective heq)

def intervalCoverRefinementTreeTasteGate :
    ChapterTasteGate IntervalCoverRefinementTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  intervalCoverRefinementTreeChapterTasteGate

theorem IntervalCoverRefinementTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      intervalCoverRefinementTreeDecodeBHist
        (intervalCoverRefinementTreeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier IntervalCoverRefinementTreeUp) ∧
        Nonempty (ChapterTasteGate IntervalCoverRefinementTreeUp) ∧
          intervalCoverRefinementTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact intervalCoverRefinementTreeDecode_encode_bhist
  · constructor
    · exact ⟨intervalCoverRefinementTreeBHistCarrier⟩
    · constructor
      · exact ⟨intervalCoverRefinementTreeChapterTasteGate⟩
      · rfl

end BEDC.Derived.IntervalCoverRefinementTreeUp
