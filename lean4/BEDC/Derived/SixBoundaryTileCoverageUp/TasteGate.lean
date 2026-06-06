import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SixBoundaryTileCoverageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SixBoundaryTileCoverageUp : Type where
  | mk (W T G R A H C P N : BHist) : SixBoundaryTileCoverageUp
  deriving DecidableEq

def sixBoundaryTileCoverageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sixBoundaryTileCoverageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sixBoundaryTileCoverageEncodeBHist h

def sixBoundaryTileCoverageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sixBoundaryTileCoverageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sixBoundaryTileCoverageDecodeBHist tail)

private theorem SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      sixBoundaryTileCoverageDecodeBHist
        (sixBoundaryTileCoverageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sixBoundaryTileCoverageFields : SixBoundaryTileCoverageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SixBoundaryTileCoverageUp.mk W T G R A H C P N => [W, T, G, R, A, H, C, P, N]

def sixBoundaryTileCoverageToEventFlow : SixBoundaryTileCoverageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sixBoundaryTileCoverageFields x).map sixBoundaryTileCoverageEncodeBHist

private def SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault index rest

def sixBoundaryTileCoverageFromEventFlow
    (ef : EventFlow) : Option SixBoundaryTileCoverageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SixBoundaryTileCoverageUp.mk
      (sixBoundaryTileCoverageDecodeBHist
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (sixBoundaryTileCoverageDecodeBHist
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (sixBoundaryTileCoverageDecodeBHist
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (sixBoundaryTileCoverageDecodeBHist
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (sixBoundaryTileCoverageDecodeBHist
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (sixBoundaryTileCoverageDecodeBHist
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (sixBoundaryTileCoverageDecodeBHist
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (sixBoundaryTileCoverageDecodeBHist
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (sixBoundaryTileCoverageDecodeBHist
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_eventAtDefault 8 ef)))

private theorem SixBoundaryTileCoverageTasteGate_single_carrier_alignment_round_trip
    (x : SixBoundaryTileCoverageUp) :
    sixBoundaryTileCoverageFromEventFlow
      (sixBoundaryTileCoverageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W T G R A H C P N =>
      change
        some
          (SixBoundaryTileCoverageUp.mk
            (sixBoundaryTileCoverageDecodeBHist (sixBoundaryTileCoverageEncodeBHist W))
            (sixBoundaryTileCoverageDecodeBHist (sixBoundaryTileCoverageEncodeBHist T))
            (sixBoundaryTileCoverageDecodeBHist (sixBoundaryTileCoverageEncodeBHist G))
            (sixBoundaryTileCoverageDecodeBHist (sixBoundaryTileCoverageEncodeBHist R))
            (sixBoundaryTileCoverageDecodeBHist (sixBoundaryTileCoverageEncodeBHist A))
            (sixBoundaryTileCoverageDecodeBHist (sixBoundaryTileCoverageEncodeBHist H))
            (sixBoundaryTileCoverageDecodeBHist (sixBoundaryTileCoverageEncodeBHist C))
            (sixBoundaryTileCoverageDecodeBHist (sixBoundaryTileCoverageEncodeBHist P))
            (sixBoundaryTileCoverageDecodeBHist (sixBoundaryTileCoverageEncodeBHist N))) =
          some (SixBoundaryTileCoverageUp.mk W T G R A H C P N)
      rw [SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode W,
        SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode T,
        SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode G,
        SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode R,
        SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode A,
        SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode H,
        SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode C,
        SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode P,
        SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode N]

private theorem SixBoundaryTileCoverageTasteGate_single_carrier_alignment_injective
    {x y : SixBoundaryTileCoverageUp} :
    sixBoundaryTileCoverageToEventFlow x = sixBoundaryTileCoverageToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sixBoundaryTileCoverageFromEventFlow (sixBoundaryTileCoverageToEventFlow x) =
        sixBoundaryTileCoverageFromEventFlow (sixBoundaryTileCoverageToEventFlow y) :=
    congrArg sixBoundaryTileCoverageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_round_trip y)))

private theorem SixBoundaryTileCoverageTasteGate_single_carrier_alignment_fields :
    ∀ x y : SixBoundaryTileCoverageUp,
      sixBoundaryTileCoverageFields x = sixBoundaryTileCoverageFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W₁ T₁ G₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk W₂ T₂ G₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance sixBoundaryTileCoverageBHistCarrier : BHistCarrier SixBoundaryTileCoverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sixBoundaryTileCoverageToEventFlow
  fromEventFlow := sixBoundaryTileCoverageFromEventFlow

instance sixBoundaryTileCoverageChapterTasteGate :
    ChapterTasteGate SixBoundaryTileCoverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sixBoundaryTileCoverageFromEventFlow (sixBoundaryTileCoverageToEventFlow x) =
      some x
    exact SixBoundaryTileCoverageTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SixBoundaryTileCoverageTasteGate_single_carrier_alignment_injective heq)

instance sixBoundaryTileCoverageFieldFaithful :
    FieldFaithful SixBoundaryTileCoverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sixBoundaryTileCoverageFields
  field_faithful := SixBoundaryTileCoverageTasteGate_single_carrier_alignment_fields

instance sixBoundaryTileCoverageNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SixBoundaryTileCoverageUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SixBoundaryTileCoverageUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SixBoundaryTileCoverageUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def SixBoundaryTileCoverageTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate SixBoundaryTileCoverageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sixBoundaryTileCoverageChapterTasteGate

theorem SixBoundaryTileCoverageTasteGate_single_carrier_alignment :
    (∀ h : BHist, sixBoundaryTileCoverageDecodeBHist
      (sixBoundaryTileCoverageEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate SixBoundaryTileCoverageUp) ∧
        Nonempty (FieldFaithful SixBoundaryTileCoverageUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial SixBoundaryTileCoverageUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SixBoundaryTileCoverageTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨sixBoundaryTileCoverageChapterTasteGate⟩
    · constructor
      · exact ⟨sixBoundaryTileCoverageFieldFaithful⟩
      · exact ⟨sixBoundaryTileCoverageNontrivial⟩

end BEDC.Derived.SixBoundaryTileCoverageUp
