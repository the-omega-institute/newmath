import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HenselLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HenselLemmaUp : Type where
  | mk (K R F P A V N E T C Q L : BHist) : HenselLemmaUp
  deriving DecidableEq

def henselLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: henselLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: henselLemmaEncodeBHist h

def henselLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (henselLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (henselLemmaDecodeBHist tail)

private theorem henselLemmaDecodeEncode :
    ∀ h : BHist, henselLemmaDecodeBHist (henselLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def henselLemmaFields : HenselLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HenselLemmaUp.mk K R F P A V N E T C Q L => [K, R, F, P, A, V, N, E, T, C, Q, L]

def henselLemmaToEventFlow : HenselLemmaUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (henselLemmaFields x).map henselLemmaEncodeBHist

private def henselLemmaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => henselLemmaEventAtDefault index rest

def henselLemmaFromEventFlow (ef : EventFlow) : Option HenselLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HenselLemmaUp.mk
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 0 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 1 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 2 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 3 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 4 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 5 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 6 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 7 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 8 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 9 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 10 ef))
      (henselLemmaDecodeBHist (henselLemmaEventAtDefault 11 ef)))

private theorem henselLemma_round_trip :
    ∀ x : HenselLemmaUp,
      henselLemmaFromEventFlow (henselLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K R F P A V N E T C Q L =>
      change
        some
          (HenselLemmaUp.mk
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist K))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist R))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist F))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist P))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist A))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist V))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist N))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist E))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist T))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist C))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist Q))
            (henselLemmaDecodeBHist (henselLemmaEncodeBHist L))) =
          some (HenselLemmaUp.mk K R F P A V N E T C Q L)
      rw [henselLemmaDecodeEncode K, henselLemmaDecodeEncode R, henselLemmaDecodeEncode F,
        henselLemmaDecodeEncode P, henselLemmaDecodeEncode A, henselLemmaDecodeEncode V,
        henselLemmaDecodeEncode N, henselLemmaDecodeEncode E, henselLemmaDecodeEncode T,
        henselLemmaDecodeEncode C, henselLemmaDecodeEncode Q, henselLemmaDecodeEncode L]

private theorem henselLemmaToEventFlow_injective {x y : HenselLemmaUp} :
    henselLemmaToEventFlow x = henselLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      henselLemmaFromEventFlow (henselLemmaToEventFlow x) =
        henselLemmaFromEventFlow (henselLemmaToEventFlow y) :=
    congrArg henselLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (henselLemma_round_trip x).symm
      (Eq.trans hread (henselLemma_round_trip y)))

private theorem henselLemmaFieldFaithfulProof :
    ∀ x y : HenselLemmaUp, henselLemmaFields x = henselLemmaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk K₁ R₁ F₁ P₁ A₁ V₁ N₁ E₁ T₁ C₁ Q₁ L₁ =>
      cases y with
      | mk K₂ R₂ F₂ P₂ A₂ V₂ N₂ E₂ T₂ C₂ Q₂ L₂ =>
          change [K₁, R₁, F₁, P₁, A₁, V₁, N₁, E₁, T₁, C₁, Q₁, L₁] =
            [K₂, R₂, F₂, P₂, A₂, V₂, N₂, E₂, T₂, C₂, Q₂, L₂] at h
          cases h
          rfl

instance henselLemmaBHistCarrier : BHistCarrier HenselLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := henselLemmaToEventFlow
  fromEventFlow := henselLemmaFromEventFlow

instance henselLemmaChapterTasteGate :
    ChapterTasteGate HenselLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change henselLemmaFromEventFlow (henselLemmaToEventFlow x) = some x
    exact henselLemma_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (henselLemmaToEventFlow_injective heq)

instance henselLemmaFieldFaithful : FieldFaithful HenselLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := henselLemmaFields
  field_faithful := henselLemmaFieldFaithfulProof

instance henselLemmaNontrivial : Nontrivial HenselLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HenselLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      HenselLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem HenselLemmaTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HenselLemmaUp) ∧
      Nonempty (FieldFaithful HenselLemmaUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HenselLemmaUp) ∧
          (∀ h : BHist, henselLemmaDecodeBHist (henselLemmaEncodeBHist h) = h) ∧
            (∀ x : HenselLemmaUp,
              henselLemmaFromEventFlow (henselLemmaToEventFlow x) = some x) ∧
              (∀ x y : HenselLemmaUp,
                henselLemmaToEventFlow x = henselLemmaToEventFlow y → x = y) ∧
                henselLemmaEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨henselLemmaChapterTasteGate⟩,
      ⟨henselLemmaFieldFaithful⟩,
      ⟨henselLemmaNontrivial⟩,
      henselLemmaDecodeEncode,
      henselLemma_round_trip,
      by
        intro x y heq
        exact henselLemmaToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.HenselLemmaUp
