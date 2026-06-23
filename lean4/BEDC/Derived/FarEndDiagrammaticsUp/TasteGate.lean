import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FarEndDiagrammaticsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FarEndDiagrammaticsUp : Type where
  | mk (S L G B U H C P N : BHist) : FarEndDiagrammaticsUp
  deriving DecidableEq

def farEndDiagrammaticsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: farEndDiagrammaticsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: farEndDiagrammaticsEncodeBHist h

def farEndDiagrammaticsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (farEndDiagrammaticsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (farEndDiagrammaticsDecodeBHist tail)

private theorem FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def farEndDiagrammaticsFields : FarEndDiagrammaticsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FarEndDiagrammaticsUp.mk S L G B U H C P N => [S, L, G, B, U, H, C, P, N]

def farEndDiagrammaticsToEventFlow : FarEndDiagrammaticsUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (farEndDiagrammaticsFields x).map farEndDiagrammaticsEncodeBHist

private def farEndDiagrammaticsRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => farEndDiagrammaticsRawAt n rest

def farEndDiagrammaticsFromEventFlow : EventFlow → Option FarEndDiagrammaticsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (FarEndDiagrammaticsUp.mk
        (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsRawAt 0 flow))
        (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsRawAt 1 flow))
        (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsRawAt 2 flow))
        (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsRawAt 3 flow))
        (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsRawAt 4 flow))
        (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsRawAt 5 flow))
        (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsRawAt 6 flow))
        (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsRawAt 7 flow))
        (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsRawAt 8 flow)))

private theorem FarEndDiagrammaticsTasteGate_single_carrier_alignment_round_trip
    (x : FarEndDiagrammaticsUp) :
    farEndDiagrammaticsFromEventFlow (farEndDiagrammaticsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S L G B U H C P N =>
      change
        some
            (FarEndDiagrammaticsUp.mk
              (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist S))
              (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist L))
              (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist G))
              (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist B))
              (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist U))
              (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist H))
              (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist C))
              (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist P))
              (farEndDiagrammaticsDecodeBHist (farEndDiagrammaticsEncodeBHist N))) =
          some (FarEndDiagrammaticsUp.mk S L G B U H C P N)
      rw [FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode S,
        FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode L,
        FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode G,
        FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode B,
        FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode U,
        FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode H,
        FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode C,
        FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode P,
        FarEndDiagrammaticsTasteGate_single_carrier_alignment_decode N]

private theorem FarEndDiagrammaticsTasteGate_single_carrier_alignment_injective
    {x y : FarEndDiagrammaticsUp} :
    farEndDiagrammaticsToEventFlow x = farEndDiagrammaticsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      farEndDiagrammaticsFromEventFlow (farEndDiagrammaticsToEventFlow x) =
        farEndDiagrammaticsFromEventFlow (farEndDiagrammaticsToEventFlow y) :=
    congrArg farEndDiagrammaticsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FarEndDiagrammaticsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FarEndDiagrammaticsTasteGate_single_carrier_alignment_round_trip y)))

private theorem FarEndDiagrammaticsTasteGate_single_carrier_alignment_fields :
    ∀ x y : FarEndDiagrammaticsUp,
      farEndDiagrammaticsFields x = farEndDiagrammaticsFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ L₁ G₁ B₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ L₂ G₂ B₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance farEndDiagrammaticsBHistCarrier : BHistCarrier FarEndDiagrammaticsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := farEndDiagrammaticsToEventFlow
  fromEventFlow := farEndDiagrammaticsFromEventFlow

instance farEndDiagrammaticsChapterTasteGate :
    ChapterTasteGate FarEndDiagrammaticsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change farEndDiagrammaticsFromEventFlow (farEndDiagrammaticsToEventFlow x) = some x
    exact FarEndDiagrammaticsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FarEndDiagrammaticsTasteGate_single_carrier_alignment_injective heq)

instance farEndDiagrammaticsFieldFaithful : FieldFaithful FarEndDiagrammaticsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := farEndDiagrammaticsFields
  field_faithful := FarEndDiagrammaticsTasteGate_single_carrier_alignment_fields

instance farEndDiagrammaticsNontrivial : Nontrivial FarEndDiagrammaticsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FarEndDiagrammaticsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FarEndDiagrammaticsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem FarEndDiagrammaticsTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FarEndDiagrammaticsUp) ∧
      Nonempty (ChapterTasteGate FarEndDiagrammaticsUp) ∧
        Nonempty (FieldFaithful FarEndDiagrammaticsUp) ∧
          Nonempty (Nontrivial FarEndDiagrammaticsUp) ∧
            farEndDiagrammaticsFields
                (FarEndDiagrammaticsUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty) =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
              FarEndDiagrammaticsUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty ≠
                FarEndDiagrammaticsUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨farEndDiagrammaticsBHistCarrier⟩,
      ⟨⟨farEndDiagrammaticsChapterTasteGate⟩,
        ⟨⟨farEndDiagrammaticsFieldFaithful⟩,
          ⟨⟨farEndDiagrammaticsNontrivial⟩,
            ⟨rfl, by
              intro h
              cases h⟩⟩⟩⟩⟩

end BEDC.Derived.FarEndDiagrammaticsUp
