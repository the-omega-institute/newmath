import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FreeGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FreeGroupUp : Type where
  | mk (G S W R M I U J H C P N : BHist) : FreeGroupUp
  deriving DecidableEq

def freeGroupEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: freeGroupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: freeGroupEncodeBHist h

def freeGroupDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (freeGroupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (freeGroupDecodeBHist tail)

private theorem FreeGroupTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, freeGroupDecodeBHist (freeGroupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def freeGroupFields : FreeGroupUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FreeGroupUp.mk G S W R M I U J H C P N => [G, S, W, R, M, I, U, J, H, C, P, N]

def freeGroupToEventFlow : FreeGroupUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (freeGroupFields x).map freeGroupEncodeBHist

private def freeGroupEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => freeGroupEventAt index rest

def freeGroupFromEventFlow (ef : EventFlow) : Option FreeGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FreeGroupUp.mk
      (freeGroupDecodeBHist (freeGroupEventAt 0 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 1 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 2 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 3 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 4 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 5 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 6 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 7 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 8 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 9 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 10 ef))
      (freeGroupDecodeBHist (freeGroupEventAt 11 ef)))

private theorem FreeGroupTasteGate_single_carrier_alignment_round_trip
    (x : FreeGroupUp) :
    freeGroupFromEventFlow (freeGroupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G S W R M I U J H C P N =>
      change
        some
          (FreeGroupUp.mk
            (freeGroupDecodeBHist (freeGroupEncodeBHist G))
            (freeGroupDecodeBHist (freeGroupEncodeBHist S))
            (freeGroupDecodeBHist (freeGroupEncodeBHist W))
            (freeGroupDecodeBHist (freeGroupEncodeBHist R))
            (freeGroupDecodeBHist (freeGroupEncodeBHist M))
            (freeGroupDecodeBHist (freeGroupEncodeBHist I))
            (freeGroupDecodeBHist (freeGroupEncodeBHist U))
            (freeGroupDecodeBHist (freeGroupEncodeBHist J))
            (freeGroupDecodeBHist (freeGroupEncodeBHist H))
            (freeGroupDecodeBHist (freeGroupEncodeBHist C))
            (freeGroupDecodeBHist (freeGroupEncodeBHist P))
            (freeGroupDecodeBHist (freeGroupEncodeBHist N))) =
          some (FreeGroupUp.mk G S W R M I U J H C P N)
      rw [FreeGroupTasteGate_single_carrier_alignment_decode_encode G,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode S,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode W,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode R,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode M,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode I,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode U,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode J,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode H,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode C,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode P,
        FreeGroupTasteGate_single_carrier_alignment_decode_encode N]

private theorem FreeGroupTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FreeGroupUp} :
    freeGroupToEventFlow x = freeGroupToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      freeGroupFromEventFlow (freeGroupToEventFlow x) =
        freeGroupFromEventFlow (freeGroupToEventFlow y) :=
    congrArg freeGroupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FreeGroupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FreeGroupTasteGate_single_carrier_alignment_round_trip y)))

private theorem FreeGroup_field_faithful :
    ∀ x y : FreeGroupUp, freeGroupFields x = freeGroupFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ S₁ W₁ R₁ M₁ I₁ U₁ J₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk G₂ S₂ W₂ R₂ M₂ I₂ U₂ J₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hG t1
          injection t1 with hS t2
          injection t2 with hW t3
          injection t3 with hR t4
          injection t4 with hM t5
          injection t5 with hI t6
          injection t6 with hU t7
          injection t7 with hJ t8
          injection t8 with hH t9
          injection t9 with hC t10
          injection t10 with hP t11
          injection t11 with hN _
          cases hG
          cases hS
          cases hW
          cases hR
          cases hM
          cases hI
          cases hU
          cases hJ
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance freeGroupBHistCarrier : BHistCarrier FreeGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := freeGroupToEventFlow
  fromEventFlow := freeGroupFromEventFlow

instance freeGroupChapterTasteGate : ChapterTasteGate FreeGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change freeGroupFromEventFlow (freeGroupToEventFlow x) = some x
    exact FreeGroupTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FreeGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def FreeGroupTasteGate_single_carrier_alignment_taste_gate : ChapterTasteGate FreeGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  freeGroupChapterTasteGate

instance freeGroupFieldFaithful : FieldFaithful FreeGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := freeGroupFields
  field_faithful := FreeGroup_field_faithful

instance freeGroupNontrivial : Nontrivial FreeGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FreeGroupUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FreeGroupUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FreeGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  freeGroupChapterTasteGate

theorem FreeGroupTasteGate_single_carrier_alignment :
    (forall h : BHist, freeGroupDecodeBHist (freeGroupEncodeBHist h) = h) ∧
      (forall x : FreeGroupUp, freeGroupFromEventFlow (freeGroupToEventFlow x) = some x) ∧
        (forall x y : FreeGroupUp, freeGroupToEventFlow x = freeGroupToEventFlow y -> x = y) ∧
          freeGroupEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FreeGroupTasteGate_single_carrier_alignment_decode_encode,
      FreeGroupTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FreeGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FreeGroupUp
