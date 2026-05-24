import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CollisionKernelUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CollisionKernelUp : Type where
  | mk (W F L M I S H C P N : BHist) : CollisionKernelUp
  deriving DecidableEq

def collisionKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: collisionKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: collisionKernelEncodeBHist h

def collisionKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (collisionKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (collisionKernelDecodeBHist tail)

private theorem collisionKernelDecode_encode :
    ∀ h : BHist, collisionKernelDecodeBHist (collisionKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def collisionKernelFields : CollisionKernelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CollisionKernelUp.mk W F L M I S H C P N => [W, F, L, M, I, S, H, C, P, N]

def collisionKernelToEventFlow : CollisionKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map collisionKernelEncodeBHist (collisionKernelFields x)

private def collisionKernelRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => collisionKernelRawAt index rest

def collisionKernelFromEventFlow (flow : EventFlow) : Option CollisionKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CollisionKernelUp.mk
      (collisionKernelDecodeBHist (collisionKernelRawAt 0 flow))
      (collisionKernelDecodeBHist (collisionKernelRawAt 1 flow))
      (collisionKernelDecodeBHist (collisionKernelRawAt 2 flow))
      (collisionKernelDecodeBHist (collisionKernelRawAt 3 flow))
      (collisionKernelDecodeBHist (collisionKernelRawAt 4 flow))
      (collisionKernelDecodeBHist (collisionKernelRawAt 5 flow))
      (collisionKernelDecodeBHist (collisionKernelRawAt 6 flow))
      (collisionKernelDecodeBHist (collisionKernelRawAt 7 flow))
      (collisionKernelDecodeBHist (collisionKernelRawAt 8 flow))
      (collisionKernelDecodeBHist (collisionKernelRawAt 9 flow)))

private theorem collisionKernel_round_trip :
    ∀ x : CollisionKernelUp,
      collisionKernelFromEventFlow (collisionKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W F L M I S H C P N =>
      change
        some
          (CollisionKernelUp.mk
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist W))
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist F))
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist L))
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist M))
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist I))
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist S))
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist H))
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist C))
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist P))
            (collisionKernelDecodeBHist (collisionKernelEncodeBHist N))) =
          some (CollisionKernelUp.mk W F L M I S H C P N)
      rw [collisionKernelDecode_encode W, collisionKernelDecode_encode F,
        collisionKernelDecode_encode L, collisionKernelDecode_encode M,
        collisionKernelDecode_encode I, collisionKernelDecode_encode S,
        collisionKernelDecode_encode H, collisionKernelDecode_encode C,
        collisionKernelDecode_encode P, collisionKernelDecode_encode N]

private theorem collisionKernelToEventFlow_injective {x y : CollisionKernelUp} :
    collisionKernelToEventFlow x = collisionKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      collisionKernelFromEventFlow (collisionKernelToEventFlow x) =
        collisionKernelFromEventFlow (collisionKernelToEventFlow y) :=
    congrArg collisionKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (collisionKernel_round_trip x).symm
      (Eq.trans hread (collisionKernel_round_trip y)))

private theorem collisionKernel_fields_faithful :
    ∀ x y : CollisionKernelUp, collisionKernelFields x = collisionKernelFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk W₁ F₁ L₁ M₁ I₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk W₂ F₂ L₂ M₂ I₂ S₂ H₂ C₂ P₂ N₂ =>
          simp only [collisionKernelFields] at h
          cases h
          rfl

instance collisionKernelBHistCarrier : BHistCarrier CollisionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := collisionKernelToEventFlow
  fromEventFlow := collisionKernelFromEventFlow

instance collisionKernelChapterTasteGate : ChapterTasteGate CollisionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change collisionKernelFromEventFlow (collisionKernelToEventFlow x) = some x
    exact collisionKernel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (collisionKernelToEventFlow_injective heq)

instance collisionKernelFieldFaithful : FieldFaithful CollisionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := collisionKernelFields
  field_faithful := collisionKernel_fields_faithful

instance collisionKernelNontrivial : Nontrivial CollisionKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CollisionKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CollisionKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CollisionKernelTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CollisionKernelUp) ∧
      Nonempty (FieldFaithful CollisionKernelUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CollisionKernelUp) ∧
          (∀ h : BHist, collisionKernelDecodeBHist (collisionKernelEncodeBHist h) = h) ∧
            (∀ x : CollisionKernelUp,
              collisionKernelFromEventFlow (collisionKernelToEventFlow x) = some x) ∧
              (∀ x y : CollisionKernelUp,
                collisionKernelToEventFlow x = collisionKernelToEventFlow y → x = y) ∧
                collisionKernelEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨collisionKernelChapterTasteGate⟩,
      ⟨collisionKernelFieldFaithful⟩,
      ⟨collisionKernelNontrivial⟩,
      collisionKernelDecode_encode,
      collisionKernel_round_trip,
      by
        intro x y heq
        exact collisionKernelToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CollisionKernelUp.TasteGate
