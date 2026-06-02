import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DnaWindowSixBoundaryTileUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DnaWindowSixBoundaryTileUp : Type where
  | mk (W M B I S L H C P N : BHist) : DnaWindowSixBoundaryTileUp
  deriving DecidableEq

def dnaWindowSixBoundaryTileEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dnaWindowSixBoundaryTileEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dnaWindowSixBoundaryTileEncodeBHist h

def dnaWindowSixBoundaryTileDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dnaWindowSixBoundaryTileDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dnaWindowSixBoundaryTileDecodeBHist tail)

private theorem DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dnaWindowSixBoundaryTileFields : DnaWindowSixBoundaryTileUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DnaWindowSixBoundaryTileUp.mk W M B I S L H C P N => [W, M, B, I, S, L, H, C, P, N]

def dnaWindowSixBoundaryTileToEventFlow : DnaWindowSixBoundaryTileUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dnaWindowSixBoundaryTileFields x).map dnaWindowSixBoundaryTileEncodeBHist

private def dnaWindowSixBoundaryTileEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dnaWindowSixBoundaryTileEventAt index rest

def dnaWindowSixBoundaryTileFromEventFlow : EventFlow → Option DnaWindowSixBoundaryTileUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DnaWindowSixBoundaryTileUp.mk
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 0 ef))
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 1 ef))
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 2 ef))
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 3 ef))
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 4 ef))
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 5 ef))
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 6 ef))
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 7 ef))
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 8 ef))
          (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEventAt 9 ef)))

private theorem DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DnaWindowSixBoundaryTileUp,
      dnaWindowSixBoundaryTileFromEventFlow (dnaWindowSixBoundaryTileToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W M B I S L H C P N =>
      change
        some
          (DnaWindowSixBoundaryTileUp.mk
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist W))
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist M))
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist B))
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist I))
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist S))
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist L))
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist H))
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist C))
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist P))
            (dnaWindowSixBoundaryTileDecodeBHist (dnaWindowSixBoundaryTileEncodeBHist N))) =
          some (DnaWindowSixBoundaryTileUp.mk W M B I S L H C P N)
      rw [DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode W,
        DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode M,
        DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode B,
        DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode I,
        DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode S,
        DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode L,
        DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode H,
        DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode C,
        DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode P,
        DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode N]

private theorem DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DnaWindowSixBoundaryTileUp} :
    dnaWindowSixBoundaryTileToEventFlow x = dnaWindowSixBoundaryTileToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dnaWindowSixBoundaryTileFromEventFlow (dnaWindowSixBoundaryTileToEventFlow x) =
        dnaWindowSixBoundaryTileFromEventFlow (dnaWindowSixBoundaryTileToEventFlow y) :=
    congrArg dnaWindowSixBoundaryTileFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_round_trip y)))

private theorem DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : DnaWindowSixBoundaryTileUp,
      dnaWindowSixBoundaryTileFields x = dnaWindowSixBoundaryTileFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk W₁ M₁ B₁ I₁ S₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk W₂ M₂ B₂ I₂ S₂ L₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance dnaWindowSixBoundaryTileBHistCarrier : BHistCarrier DnaWindowSixBoundaryTileUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dnaWindowSixBoundaryTileToEventFlow
  fromEventFlow := dnaWindowSixBoundaryTileFromEventFlow

instance dnaWindowSixBoundaryTileChapterTasteGate :
    ChapterTasteGate DnaWindowSixBoundaryTileUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dnaWindowSixBoundaryTileFromEventFlow (dnaWindowSixBoundaryTileToEventFlow x) =
      some x
    exact DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dnaWindowSixBoundaryTileFieldFaithful : FieldFaithful DnaWindowSixBoundaryTileUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dnaWindowSixBoundaryTileFields
  field_faithful := DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_field_faithful

instance dnaWindowSixBoundaryTileNontrivial : Nontrivial DnaWindowSixBoundaryTileUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DnaWindowSixBoundaryTileUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DnaWindowSixBoundaryTileUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment :
    (∀ h : BHist, dnaWindowSixBoundaryTileDecodeBHist
      (dnaWindowSixBoundaryTileEncodeBHist h) = h) ∧
      (∀ x : DnaWindowSixBoundaryTileUp,
        dnaWindowSixBoundaryTileFromEventFlow (dnaWindowSixBoundaryTileToEventFlow x) =
          some x) ∧
        (∀ x y : DnaWindowSixBoundaryTileUp,
          dnaWindowSixBoundaryTileToEventFlow x = dnaWindowSixBoundaryTileToEventFlow y →
            x = y) ∧
          dnaWindowSixBoundaryTileEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact DnaWindowSixBoundaryTileTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.DnaWindowSixBoundaryTileUp
