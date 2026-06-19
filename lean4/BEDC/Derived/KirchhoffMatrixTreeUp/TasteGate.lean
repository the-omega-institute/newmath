import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KirchhoffMatrixTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KirchhoffMatrixTreeUp : Type where
  | mk (G E L M D S T H C P N : BHist) : KirchhoffMatrixTreeUp
  deriving DecidableEq

def kirchhoffMatrixTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kirchhoffMatrixTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kirchhoffMatrixTreeEncodeBHist h

def kirchhoffMatrixTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kirchhoffMatrixTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kirchhoffMatrixTreeDecodeBHist tail)

private theorem KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def kirchhoffMatrixTreeFields : KirchhoffMatrixTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KirchhoffMatrixTreeUp.mk G E L M D S T H C P N => [G, E, L, M, D, S, T, H, C, P, N]

def kirchhoffMatrixTreeToEventFlow : KirchhoffMatrixTreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kirchhoffMatrixTreeFields x).map kirchhoffMatrixTreeEncodeBHist

private def kirchhoffMatrixTreeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kirchhoffMatrixTreeEventAt index rest

def kirchhoffMatrixTreeFromEventFlow (ef : EventFlow) :
    Option KirchhoffMatrixTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KirchhoffMatrixTreeUp.mk
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 0 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 1 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 2 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 3 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 4 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 5 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 6 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 7 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 8 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 9 ef))
      (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEventAt 10 ef)))

private theorem KirchhoffMatrixTreeTasteGate_single_carrier_alignment_round_trip
    (x : KirchhoffMatrixTreeUp) :
    kirchhoffMatrixTreeFromEventFlow (kirchhoffMatrixTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G E L M D S T H C P N =>
      change
        some
          (KirchhoffMatrixTreeUp.mk
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist G))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist E))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist L))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist M))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist D))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist S))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist T))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist H))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist C))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist P))
            (kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist N))) =
          some (KirchhoffMatrixTreeUp.mk G E L M D S T H C P N)
      rw [KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode G,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode E,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode L,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode M,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode D,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode S,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode T,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode H,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode C,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode P,
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode N]

private theorem KirchhoffMatrixTreeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KirchhoffMatrixTreeUp} :
    kirchhoffMatrixTreeToEventFlow x = kirchhoffMatrixTreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kirchhoffMatrixTreeFromEventFlow (kirchhoffMatrixTreeToEventFlow x) =
        kirchhoffMatrixTreeFromEventFlow (kirchhoffMatrixTreeToEventFlow y) :=
    congrArg kirchhoffMatrixTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KirchhoffMatrixTreeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KirchhoffMatrixTreeTasteGate_single_carrier_alignment_round_trip y)))

private theorem KirchhoffMatrixTreeTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : KirchhoffMatrixTreeUp, kirchhoffMatrixTreeFields x = kirchhoffMatrixTreeFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ E₁ L₁ M₁ D₁ S₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk G₂ E₂ L₂ M₂ D₂ S₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance kirchhoffMatrixTreeBHistCarrier : BHistCarrier KirchhoffMatrixTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kirchhoffMatrixTreeToEventFlow
  fromEventFlow := kirchhoffMatrixTreeFromEventFlow

instance kirchhoffMatrixTreeChapterTasteGate : ChapterTasteGate KirchhoffMatrixTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kirchhoffMatrixTreeFromEventFlow (kirchhoffMatrixTreeToEventFlow x) = some x
    exact KirchhoffMatrixTreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KirchhoffMatrixTreeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance kirchhoffMatrixTreeFieldFaithful : FieldFaithful KirchhoffMatrixTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kirchhoffMatrixTreeFields
  field_faithful := KirchhoffMatrixTreeTasteGate_single_carrier_alignment_fields_faithful

instance kirchhoffMatrixTreeNontrivial : Nontrivial KirchhoffMatrixTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KirchhoffMatrixTreeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      KirchhoffMatrixTreeUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def KirchhoffMatrixTreeTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate KirchhoffMatrixTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kirchhoffMatrixTreeChapterTasteGate

theorem KirchhoffMatrixTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist, kirchhoffMatrixTreeDecodeBHist (kirchhoffMatrixTreeEncodeBHist h) = h) ∧
      (∀ x : KirchhoffMatrixTreeUp,
        kirchhoffMatrixTreeFromEventFlow (kirchhoffMatrixTreeToEventFlow x) = some x) ∧
        (∀ x y : KirchhoffMatrixTreeUp,
          kirchhoffMatrixTreeToEventFlow x = kirchhoffMatrixTreeToEventFlow y → x = y) ∧
          kirchhoffMatrixTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KirchhoffMatrixTreeTasteGate_single_carrier_alignment_decode_encode,
      KirchhoffMatrixTreeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KirchhoffMatrixTreeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.KirchhoffMatrixTreeUp
