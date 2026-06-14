import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedSetUp : Type where
  | mk
      (topology metric separatedMetric classifier openComplement metricBoundary transport replay
        provenance localName : BHist) : ClosedSetUp
  deriving DecidableEq

def closedSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedSetEncodeBHist h

def closedSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedSetDecodeBHist tail)

private theorem closedSetDecode_encode :
    ∀ h : BHist, closedSetDecodeBHist (closedSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedSetFields : ClosedSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedSetUp.mk T M S F O B H C P N => [T, M, S, F, O, B, H, C, P, N]

def closedSetToEventFlow : ClosedSetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (closedSetFields x).map closedSetEncodeBHist

private def closedSetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedSetEventAt index rest

def closedSetFromEventFlow (ef : EventFlow) : Option ClosedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedSetUp.mk
      (closedSetDecodeBHist (closedSetEventAt 0 ef))
      (closedSetDecodeBHist (closedSetEventAt 1 ef))
      (closedSetDecodeBHist (closedSetEventAt 2 ef))
      (closedSetDecodeBHist (closedSetEventAt 3 ef))
      (closedSetDecodeBHist (closedSetEventAt 4 ef))
      (closedSetDecodeBHist (closedSetEventAt 5 ef))
      (closedSetDecodeBHist (closedSetEventAt 6 ef))
      (closedSetDecodeBHist (closedSetEventAt 7 ef))
      (closedSetDecodeBHist (closedSetEventAt 8 ef))
      (closedSetDecodeBHist (closedSetEventAt 9 ef)))

private theorem closedSet_round_trip :
    ∀ x : ClosedSetUp, closedSetFromEventFlow (closedSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M S F O B H C P N =>
      change
        some
          (ClosedSetUp.mk
            (closedSetDecodeBHist (closedSetEncodeBHist T))
            (closedSetDecodeBHist (closedSetEncodeBHist M))
            (closedSetDecodeBHist (closedSetEncodeBHist S))
            (closedSetDecodeBHist (closedSetEncodeBHist F))
            (closedSetDecodeBHist (closedSetEncodeBHist O))
            (closedSetDecodeBHist (closedSetEncodeBHist B))
            (closedSetDecodeBHist (closedSetEncodeBHist H))
            (closedSetDecodeBHist (closedSetEncodeBHist C))
            (closedSetDecodeBHist (closedSetEncodeBHist P))
            (closedSetDecodeBHist (closedSetEncodeBHist N))) =
          some (ClosedSetUp.mk T M S F O B H C P N)
      rw [closedSetDecode_encode T, closedSetDecode_encode M, closedSetDecode_encode S,
        closedSetDecode_encode F, closedSetDecode_encode O, closedSetDecode_encode B,
        closedSetDecode_encode H, closedSetDecode_encode C, closedSetDecode_encode P,
        closedSetDecode_encode N]

private theorem closedSetToEventFlow_injective {x y : ClosedSetUp} :
    closedSetToEventFlow x = closedSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedSetFromEventFlow (closedSetToEventFlow x) =
        closedSetFromEventFlow (closedSetToEventFlow y) :=
    congrArg closedSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedSet_round_trip x).symm (Eq.trans hread (closedSet_round_trip y)))

private theorem closedSetFields_faithful :
    ∀ x y : ClosedSetUp, closedSetFields x = closedSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ M₁ S₁ F₁ O₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ M₂ S₂ F₂ O₂ B₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance closedSetBHistCarrier : BHistCarrier ClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedSetToEventFlow
  fromEventFlow := closedSetFromEventFlow

instance closedSetChapterTasteGate : ChapterTasteGate ClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedSetFromEventFlow (closedSetToEventFlow x) = some x
    exact closedSet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedSetToEventFlow_injective heq)

instance closedSetFieldFaithful : FieldFaithful ClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedSetFields
  field_faithful := closedSetFields_faithful

instance closedSetNontrivial : Nontrivial ClosedSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def closedSetTasteGate : ChapterTasteGate ClosedSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedSetChapterTasteGate

theorem ClosedSetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ClosedSetUp) ∧
      Nonempty (FieldFaithful ClosedSetUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ClosedSetUp) ∧
          (∀ h : BHist, closedSetDecodeBHist (closedSetEncodeBHist h) = h) ∧
            (∀ x : ClosedSetUp, closedSetFromEventFlow (closedSetToEventFlow x) = some x) ∧
              (∀ x y : ClosedSetUp, closedSetToEventFlow x = closedSetToEventFlow y → x = y) ∧
                closedSetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨closedSetChapterTasteGate⟩,
      ⟨closedSetFieldFaithful⟩,
      ⟨closedSetNontrivial⟩,
      closedSetDecode_encode,
      closedSet_round_trip,
      (fun _ _ heq => closedSetToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ClosedSetUp
