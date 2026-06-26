import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSeriesPermutationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSeriesPermutationUp : Type where
  | mk (I L Pi A W F T H C P N : BHist) : FiniteSeriesPermutationUp
  deriving DecidableEq

def finiteSeriesPermutationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSeriesPermutationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSeriesPermutationEncodeBHist h

def finiteSeriesPermutationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSeriesPermutationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSeriesPermutationDecodeBHist tail)

private theorem FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteSeriesPermutationFields : FiniteSeriesPermutationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSeriesPermutationUp.mk I L Pi A W F T H C P N =>
      [I, L, Pi, A, W, F, T, H, C, P, N]

def finiteSeriesPermutationToEventFlow : FiniteSeriesPermutationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteSeriesPermutationFields x).map finiteSeriesPermutationEncodeBHist

private def finiteSeriesPermutationEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteSeriesPermutationEventAt index rest

def finiteSeriesPermutationFromEventFlow (ef : EventFlow) : Option FiniteSeriesPermutationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteSeriesPermutationUp.mk
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 0 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 1 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 2 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 3 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 4 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 5 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 6 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 7 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 8 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 9 ef))
      (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEventAt 10 ef)))

private theorem FiniteSeriesPermutationTasteGate_single_carrier_alignment_round_trip
    (x : FiniteSeriesPermutationUp) :
    finiteSeriesPermutationFromEventFlow (finiteSeriesPermutationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I L Pi A W F T H C P N =>
      change
        some
          (FiniteSeriesPermutationUp.mk
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist I))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist L))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist Pi))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist A))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist W))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist F))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist T))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist H))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist C))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist P))
            (finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist N))) =
          some (FiniteSeriesPermutationUp.mk I L Pi A W F T H C P N)
      rw [FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode I,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode L,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode Pi,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode A,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode W,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode F,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode T,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode H,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode C,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode P,
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteSeriesPermutationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteSeriesPermutationUp} :
    finiteSeriesPermutationToEventFlow x = finiteSeriesPermutationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSeriesPermutationFromEventFlow (finiteSeriesPermutationToEventFlow x) =
        finiteSeriesPermutationFromEventFlow (finiteSeriesPermutationToEventFlow y) :=
    congrArg finiteSeriesPermutationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteSeriesPermutationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteSeriesPermutationTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteSeriesPermutationTasteGate_single_carrier_alignment_field_faithful :
    forall x y : FiniteSeriesPermutationUp,
      finiteSeriesPermutationFields x = finiteSeriesPermutationFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ L₁ Pi₁ A₁ W₁ F₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ L₂ Pi₂ A₂ W₂ F₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance finiteSeriesPermutationBHistCarrier : BHistCarrier FiniteSeriesPermutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSeriesPermutationToEventFlow
  fromEventFlow := finiteSeriesPermutationFromEventFlow

instance finiteSeriesPermutationChapterTasteGate :
    ChapterTasteGate FiniteSeriesPermutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSeriesPermutationFromEventFlow (finiteSeriesPermutationToEventFlow x) =
      some x
    exact FiniteSeriesPermutationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteSeriesPermutationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteSeriesPermutationFieldFaithful : FieldFaithful FiniteSeriesPermutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteSeriesPermutationFields
  field_faithful := FiniteSeriesPermutationTasteGate_single_carrier_alignment_field_faithful

instance finiteSeriesPermutationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteSeriesPermutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteSeriesPermutationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      FiniteSeriesPermutationUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def FiniteSeriesPermutationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FiniteSeriesPermutationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteSeriesPermutationChapterTasteGate

theorem FiniteSeriesPermutationTasteGate_single_carrier_alignment :
    (forall h : BHist,
        finiteSeriesPermutationDecodeBHist (finiteSeriesPermutationEncodeBHist h) = h) ∧
      (forall x : FiniteSeriesPermutationUp,
        finiteSeriesPermutationFromEventFlow (finiteSeriesPermutationToEventFlow x) = some x) ∧
      (forall x y : FiniteSeriesPermutationUp,
        finiteSeriesPermutationToEventFlow x = finiteSeriesPermutationToEventFlow y -> x = y) ∧
      finiteSeriesPermutationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteSeriesPermutationTasteGate_single_carrier_alignment_decode_encode,
      FiniteSeriesPermutationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteSeriesPermutationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteSeriesPermutationUp
