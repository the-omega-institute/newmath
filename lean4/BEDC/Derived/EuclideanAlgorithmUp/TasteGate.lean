import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EuclideanAlgorithmUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EuclideanAlgorithmUp : Type where
  | mk (I S B T Z H C P N : BHist) : EuclideanAlgorithmUp
  deriving DecidableEq

def euclideanAlgorithmEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: euclideanAlgorithmEncodeBHist h
  | BHist.e1 h => BMark.b1 :: euclideanAlgorithmEncodeBHist h

def euclideanAlgorithmDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (euclideanAlgorithmDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (euclideanAlgorithmDecodeBHist tail)

private theorem EuclideanAlgorithmTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def euclideanAlgorithmFields : EuclideanAlgorithmUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EuclideanAlgorithmUp.mk I S B T Z H C P N => [I, S, B, T, Z, H, C, P, N]

def euclideanAlgorithmToEventFlow : EuclideanAlgorithmUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (euclideanAlgorithmFields x).map euclideanAlgorithmEncodeBHist

private def euclideanAlgorithmEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => euclideanAlgorithmEventAt index rest

def euclideanAlgorithmFromEventFlow (ef : EventFlow) : Option EuclideanAlgorithmUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EuclideanAlgorithmUp.mk
      (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEventAt 0 ef))
      (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEventAt 1 ef))
      (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEventAt 2 ef))
      (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEventAt 3 ef))
      (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEventAt 4 ef))
      (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEventAt 5 ef))
      (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEventAt 6 ef))
      (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEventAt 7 ef))
      (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEventAt 8 ef)))

private theorem EuclideanAlgorithmTasteGate_single_carrier_alignment_round_trip
    (x : EuclideanAlgorithmUp) :
    euclideanAlgorithmFromEventFlow (euclideanAlgorithmToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I S B T Z H C P N =>
      change
        some
          (EuclideanAlgorithmUp.mk
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist I))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist S))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist B))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist T))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist Z))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist H))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist C))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist P))
            (euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist N))) =
          some (EuclideanAlgorithmUp.mk I S B T Z H C P N)
      rw [EuclideanAlgorithmTasteGate_single_carrier_alignment_decode I,
        EuclideanAlgorithmTasteGate_single_carrier_alignment_decode S,
        EuclideanAlgorithmTasteGate_single_carrier_alignment_decode B,
        EuclideanAlgorithmTasteGate_single_carrier_alignment_decode T,
        EuclideanAlgorithmTasteGate_single_carrier_alignment_decode Z,
        EuclideanAlgorithmTasteGate_single_carrier_alignment_decode H,
        EuclideanAlgorithmTasteGate_single_carrier_alignment_decode C,
        EuclideanAlgorithmTasteGate_single_carrier_alignment_decode P,
        EuclideanAlgorithmTasteGate_single_carrier_alignment_decode N]

private theorem EuclideanAlgorithmTasteGate_single_carrier_alignment_injective
    {x y : EuclideanAlgorithmUp} :
    euclideanAlgorithmToEventFlow x = euclideanAlgorithmToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      euclideanAlgorithmFromEventFlow (euclideanAlgorithmToEventFlow x) =
        euclideanAlgorithmFromEventFlow (euclideanAlgorithmToEventFlow y) :=
    congrArg euclideanAlgorithmFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EuclideanAlgorithmTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EuclideanAlgorithmTasteGate_single_carrier_alignment_round_trip y)))

private theorem EuclideanAlgorithmTasteGate_single_carrier_alignment_fields :
    ∀ x y : EuclideanAlgorithmUp, euclideanAlgorithmFields x = euclideanAlgorithmFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ S₁ B₁ T₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ S₂ B₂ T₂ Z₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance euclideanAlgorithmBHistCarrier : BHistCarrier EuclideanAlgorithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := euclideanAlgorithmToEventFlow
  fromEventFlow := euclideanAlgorithmFromEventFlow

instance euclideanAlgorithmChapterTasteGate : ChapterTasteGate EuclideanAlgorithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change euclideanAlgorithmFromEventFlow (euclideanAlgorithmToEventFlow x) = some x
    exact EuclideanAlgorithmTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EuclideanAlgorithmTasteGate_single_carrier_alignment_injective heq)

instance euclideanAlgorithmFieldFaithful : FieldFaithful EuclideanAlgorithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := euclideanAlgorithmFields
  field_faithful := EuclideanAlgorithmTasteGate_single_carrier_alignment_fields

instance euclideanAlgorithmNontrivial : Nontrivial EuclideanAlgorithmUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EuclideanAlgorithmUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EuclideanAlgorithmUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem EuclideanAlgorithmTasteGate_single_carrier_alignment :
    (∀ h : BHist, euclideanAlgorithmDecodeBHist (euclideanAlgorithmEncodeBHist h) = h) ∧
      (∀ x : EuclideanAlgorithmUp,
        euclideanAlgorithmFromEventFlow (euclideanAlgorithmToEventFlow x) = some x) ∧
        (∀ x y : EuclideanAlgorithmUp,
          euclideanAlgorithmToEventFlow x = euclideanAlgorithmToEventFlow y → x = y) ∧
          euclideanAlgorithmEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact EuclideanAlgorithmTasteGate_single_carrier_alignment_decode
  constructor
  · exact EuclideanAlgorithmTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact EuclideanAlgorithmTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.EuclideanAlgorithmUp
