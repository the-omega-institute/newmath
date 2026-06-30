import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LipschitzCompletionExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LipschitzCompletionExtensionUp : Type where
  | mk (D M L S Q E H C P N : BHist) : LipschitzCompletionExtensionUp
  deriving DecidableEq

def lipschitzCompletionExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lipschitzCompletionExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lipschitzCompletionExtensionEncodeBHist h

def lipschitzCompletionExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lipschitzCompletionExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lipschitzCompletionExtensionDecodeBHist tail)

private theorem LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      lipschitzCompletionExtensionDecodeBHist
        (lipschitzCompletionExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lipschitzCompletionExtensionFields :
    LipschitzCompletionExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LipschitzCompletionExtensionUp.mk D M L S Q E H C P N =>
      [D, M, L, S, Q, E, H, C, P, N]

def lipschitzCompletionExtensionToEventFlow :
    LipschitzCompletionExtensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lipschitzCompletionExtensionFields x).map
      lipschitzCompletionExtensionEncodeBHist

private def lipschitzCompletionExtensionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lipschitzCompletionExtensionEventAt index rest

def lipschitzCompletionExtensionFromEventFlow
    (ef : EventFlow) : Option LipschitzCompletionExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LipschitzCompletionExtensionUp.mk
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 0 ef))
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 1 ef))
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 2 ef))
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 3 ef))
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 4 ef))
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 5 ef))
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 6 ef))
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 7 ef))
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 8 ef))
      (lipschitzCompletionExtensionDecodeBHist (lipschitzCompletionExtensionEventAt 9 ef)))

private theorem LipschitzCompletionExtensionTasteGate_single_carrier_alignment_round_trip
    (x : LipschitzCompletionExtensionUp) :
    lipschitzCompletionExtensionFromEventFlow
      (lipschitzCompletionExtensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D M L S Q E H C P N =>
      change
        some
          (LipschitzCompletionExtensionUp.mk
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist D))
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist M))
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist L))
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist S))
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist Q))
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist E))
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist H))
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist C))
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist P))
            (lipschitzCompletionExtensionDecodeBHist
              (lipschitzCompletionExtensionEncodeBHist N))) =
          some (LipschitzCompletionExtensionUp.mk D M L S Q E H C P N)
      rw [LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode D,
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode M,
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode L,
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode S,
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode Q,
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode E,
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode H,
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode C,
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode P,
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode N]

private theorem LipschitzCompletionExtensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LipschitzCompletionExtensionUp} :
    lipschitzCompletionExtensionToEventFlow x =
      lipschitzCompletionExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lipschitzCompletionExtensionFromEventFlow
          (lipschitzCompletionExtensionToEventFlow x) =
        lipschitzCompletionExtensionFromEventFlow
          (lipschitzCompletionExtensionToEventFlow y) :=
    congrArg lipschitzCompletionExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LipschitzCompletionExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LipschitzCompletionExtensionTasteGate_single_carrier_alignment_round_trip y)))

private theorem LipschitzCompletionExtensionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LipschitzCompletionExtensionUp,
      lipschitzCompletionExtensionFields x = lipschitzCompletionExtensionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ M₁ L₁ S₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ M₂ L₂ S₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance lipschitzCompletionExtensionBHistCarrier :
    BHistCarrier LipschitzCompletionExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lipschitzCompletionExtensionToEventFlow
  fromEventFlow := lipschitzCompletionExtensionFromEventFlow

instance lipschitzCompletionExtensionChapterTasteGate :
    ChapterTasteGate LipschitzCompletionExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      lipschitzCompletionExtensionFromEventFlow
        (lipschitzCompletionExtensionToEventFlow x) = some x
    exact LipschitzCompletionExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LipschitzCompletionExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance lipschitzCompletionExtensionFieldFaithful :
    FieldFaithful LipschitzCompletionExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lipschitzCompletionExtensionFields
  field_faithful :=
    LipschitzCompletionExtensionTasteGate_single_carrier_alignment_fields_faithful

instance lipschitzCompletionExtensionNontrivial :
    Nontrivial LipschitzCompletionExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LipschitzCompletionExtensionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      LipschitzCompletionExtensionUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def LipschitzCompletionExtensionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LipschitzCompletionExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lipschitzCompletionExtensionChapterTasteGate

theorem LipschitzCompletionExtensionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      lipschitzCompletionExtensionDecodeBHist
        (lipschitzCompletionExtensionEncodeBHist h) = h) ∧
      (∀ x : LipschitzCompletionExtensionUp,
        lipschitzCompletionExtensionFromEventFlow
          (lipschitzCompletionExtensionToEventFlow x) = some x) ∧
        (∀ x y : LipschitzCompletionExtensionUp,
          lipschitzCompletionExtensionToEventFlow x =
            lipschitzCompletionExtensionToEventFlow y → x = y) ∧
          lipschitzCompletionExtensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨LipschitzCompletionExtensionTasteGate_single_carrier_alignment_decode_encode,
      LipschitzCompletionExtensionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LipschitzCompletionExtensionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LipschitzCompletionExtensionUp
