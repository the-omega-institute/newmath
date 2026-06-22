import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedDiagonalUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedDiagonalUp : Type where
  | mk (Q W R E X L H C P N : BHist) : BishopLocatedDiagonalUp

def bishopLocatedDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedDiagonalEncodeBHist h

def bishopLocatedDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedDiagonalDecodeBHist tail)

private theorem BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedDiagonalFields : BishopLocatedDiagonalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedDiagonalUp.mk Q W R E X L H C P N => [Q, W, R, E, X, L, H, C, P, N]

def bishopLocatedDiagonalToEventFlow : BishopLocatedDiagonalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopLocatedDiagonalFields x).map bishopLocatedDiagonalEncodeBHist

private def bishopLocatedDiagonalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedDiagonalEventAt index rest

def bishopLocatedDiagonalFromEventFlow (ef : EventFlow) : Option BishopLocatedDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedDiagonalUp.mk
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 0 ef))
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 1 ef))
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 2 ef))
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 3 ef))
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 4 ef))
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 5 ef))
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 6 ef))
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 7 ef))
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 8 ef))
      (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEventAt 9 ef)))

private theorem BishopLocatedDiagonalTasteGate_single_carrier_alignment_round_trip
    (x : BishopLocatedDiagonalUp) :
    bishopLocatedDiagonalFromEventFlow (bishopLocatedDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q W R E X L H C P N =>
      change
        some
          (BishopLocatedDiagonalUp.mk
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist Q))
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist W))
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist R))
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist E))
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist X))
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist L))
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist H))
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist C))
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist P))
            (bishopLocatedDiagonalDecodeBHist (bishopLocatedDiagonalEncodeBHist N))) =
          some (BishopLocatedDiagonalUp.mk Q W R E X L H C P N)
      rw [BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode Q,
        BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode W,
        BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode R,
        BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode E,
        BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode X,
        BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode L,
        BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode H,
        BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode C,
        BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode P,
        BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopLocatedDiagonalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopLocatedDiagonalUp} :
    bishopLocatedDiagonalToEventFlow x = bishopLocatedDiagonalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedDiagonalFromEventFlow (bishopLocatedDiagonalToEventFlow x) =
        bishopLocatedDiagonalFromEventFlow (bishopLocatedDiagonalToEventFlow y) :=
    congrArg bishopLocatedDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopLocatedDiagonalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedDiagonalTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopLocatedDiagonalTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopLocatedDiagonalUp,
      bishopLocatedDiagonalFields x = bishopLocatedDiagonalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q₁ W₁ R₁ E₁ X₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ W₂ R₂ E₂ X₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopLocatedDiagonalBHistCarrier : BHistCarrier BishopLocatedDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedDiagonalToEventFlow
  fromEventFlow := bishopLocatedDiagonalFromEventFlow

instance bishopLocatedDiagonalChapterTasteGate :
    ChapterTasteGate BishopLocatedDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopLocatedDiagonalFromEventFlow (bishopLocatedDiagonalToEventFlow x) = some x
    exact BishopLocatedDiagonalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedDiagonalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopLocatedDiagonalFieldFaithful : FieldFaithful BishopLocatedDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedDiagonalFields
  field_faithful := BishopLocatedDiagonalTasteGate_single_carrier_alignment_fields_faithful

theorem BishopLocatedDiagonalTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BishopLocatedDiagonalUp) ∧
      Nonempty (ChapterTasteGate BishopLocatedDiagonalUp) ∧
        Nonempty (FieldFaithful BishopLocatedDiagonalUp) ∧
          bishopLocatedDiagonalDecodeBHist
              (bishopLocatedDiagonalEncodeBHist BHist.Empty) = BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨Nonempty.intro bishopLocatedDiagonalBHistCarrier,
      Nonempty.intro bishopLocatedDiagonalChapterTasteGate,
      Nonempty.intro bishopLocatedDiagonalFieldFaithful,
      BishopLocatedDiagonalTasteGate_single_carrier_alignment_decode_encode BHist.Empty⟩

end BEDC.Derived.BishopLocatedDiagonalUp.TasteGate
