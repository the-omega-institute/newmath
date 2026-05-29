import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCauchyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCauchyFilterUp : Type where
  | mk (W T D R E H C P N : BHist) : FiniteCauchyFilterUp
  deriving DecidableEq

def finiteCauchyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCauchyFilterEncodeBHist h

def finiteCauchyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCauchyFilterDecodeBHist tail)

private theorem finiteCauchyFilterDecode_encode :
    ∀ h : BHist, finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteCauchyFilterFields : FiniteCauchyFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCauchyFilterUp.mk W T D R E H C P N => [W, T, D, R, E, H, C, P, N]

def finiteCauchyFilterToEventFlow : FiniteCauchyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCauchyFilterUp.mk W T D R E H C P N =>
      [finiteCauchyFilterEncodeBHist W, finiteCauchyFilterEncodeBHist T,
        finiteCauchyFilterEncodeBHist D, finiteCauchyFilterEncodeBHist R,
        finiteCauchyFilterEncodeBHist E, finiteCauchyFilterEncodeBHist H,
        finiteCauchyFilterEncodeBHist C, finiteCauchyFilterEncodeBHist P,
        finiteCauchyFilterEncodeBHist N]

private def finiteCauchyFilterEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteCauchyFilterEventAt index rest

def finiteCauchyFilterFromEventFlow : EventFlow → Option FiniteCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FiniteCauchyFilterUp.mk
        (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEventAt 0 ef))
        (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEventAt 1 ef))
        (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEventAt 2 ef))
        (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEventAt 3 ef))
        (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEventAt 4 ef))
        (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEventAt 5 ef))
        (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEventAt 6 ef))
        (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEventAt 7 ef))
        (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEventAt 8 ef)))

private theorem finiteCauchyFilter_round_trip :
    ∀ x : FiniteCauchyFilterUp,
      finiteCauchyFilterFromEventFlow (finiteCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W T D R E H C P N =>
      change
        some
            (FiniteCauchyFilterUp.mk
              (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist W))
              (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist T))
              (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist D))
              (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist R))
              (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist E))
              (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist H))
              (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist C))
              (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist P))
              (finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist N))) =
          some (FiniteCauchyFilterUp.mk W T D R E H C P N)
      rw [finiteCauchyFilterDecode_encode W, finiteCauchyFilterDecode_encode T,
        finiteCauchyFilterDecode_encode D, finiteCauchyFilterDecode_encode R,
        finiteCauchyFilterDecode_encode E, finiteCauchyFilterDecode_encode H,
        finiteCauchyFilterDecode_encode C, finiteCauchyFilterDecode_encode P,
        finiteCauchyFilterDecode_encode N]

private theorem finiteCauchyFilterToEventFlow_injective {x y : FiniteCauchyFilterUp} :
    finiteCauchyFilterToEventFlow x = finiteCauchyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCauchyFilterFromEventFlow (finiteCauchyFilterToEventFlow x) =
        finiteCauchyFilterFromEventFlow (finiteCauchyFilterToEventFlow y) :=
    congrArg finiteCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteCauchyFilter_round_trip x).symm
      (Eq.trans hread (finiteCauchyFilter_round_trip y)))

private theorem finiteCauchyFilterFieldFaithfulProof :
    ∀ x y : FiniteCauchyFilterUp,
      finiteCauchyFilterFields x = finiteCauchyFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W₁ T₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk W₂ T₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance finiteCauchyFilterBHistCarrier : BHistCarrier FiniteCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCauchyFilterToEventFlow
  fromEventFlow := finiteCauchyFilterFromEventFlow

instance finiteCauchyFilterChapterTasteGate : ChapterTasteGate FiniteCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteCauchyFilterFromEventFlow (finiteCauchyFilterToEventFlow x) = some x
    exact finiteCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteCauchyFilterToEventFlow_injective heq)

instance finiteCauchyFilterFieldFaithful : FieldFaithful FiniteCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteCauchyFilterFields
  field_faithful := finiteCauchyFilterFieldFaithfulProof

instance finiteCauchyFilterNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteCauchyFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteCauchyFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteCauchyFilterTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteCauchyFilterUp) ∧
      Nonempty (FieldFaithful FiniteCauchyFilterUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteCauchyFilterUp) ∧
      (∀ h : BHist, finiteCauchyFilterDecodeBHist (finiteCauchyFilterEncodeBHist h) = h) ∧
      (∀ x : FiniteCauchyFilterUp,
        finiteCauchyFilterFromEventFlow (finiteCauchyFilterToEventFlow x) = some x) ∧
      (∀ x y : FiniteCauchyFilterUp,
        finiteCauchyFilterToEventFlow x = finiteCauchyFilterToEventFlow y → x = y) ∧
      finiteCauchyFilterEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨finiteCauchyFilterChapterTasteGate⟩
  constructor
  · exact ⟨finiteCauchyFilterFieldFaithful⟩
  constructor
  · exact ⟨finiteCauchyFilterNontrivial⟩
  constructor
  · exact finiteCauchyFilterDecode_encode
  constructor
  · exact finiteCauchyFilter_round_trip
  constructor
  · intro x y
    exact finiteCauchyFilterToEventFlow_injective
  · rfl

end BEDC.Derived.FiniteCauchyFilterUp
