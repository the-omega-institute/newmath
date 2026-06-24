import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactModulusRealizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactModulusRealizerUp : Type where
  | mk (K F G Q B U H C P N : BHist) : CompactModulusRealizerUp
  deriving DecidableEq

def compactModulusRealizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactModulusRealizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactModulusRealizerEncodeBHist h

def compactModulusRealizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactModulusRealizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactModulusRealizerDecodeBHist tail)

private theorem CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactModulusRealizerFields : CompactModulusRealizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactModulusRealizerUp.mk K F G Q B U H C P N => [K, F, G, Q, B, U, H, C, P, N]

def compactModulusRealizerToEventFlow : CompactModulusRealizerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactModulusRealizerFields x).map compactModulusRealizerEncodeBHist

private def compactModulusRealizerEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactModulusRealizerEventAt index rest

def compactModulusRealizerFromEventFlow
    (ef : EventFlow) : Option CompactModulusRealizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactModulusRealizerUp.mk
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 0 ef))
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 1 ef))
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 2 ef))
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 3 ef))
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 4 ef))
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 5 ef))
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 6 ef))
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 7 ef))
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 8 ef))
      (compactModulusRealizerDecodeBHist (compactModulusRealizerEventAt 9 ef)))

private theorem CompactModulusRealizerTasteGate_single_carrier_alignment_round_trip
    (x : CompactModulusRealizerUp) :
    compactModulusRealizerFromEventFlow (compactModulusRealizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F G Q B U H C P N =>
      change
        some
          (CompactModulusRealizerUp.mk
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist K))
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist F))
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist G))
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist Q))
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist B))
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist U))
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist H))
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist C))
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist P))
            (compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist N))) =
          some (CompactModulusRealizerUp.mk K F G Q B U H C P N)
      rw [CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode K,
        CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode F,
        CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode G,
        CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode Q,
        CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode B,
        CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode U,
        CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode H,
        CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode C,
        CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode P,
        CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode N]

private theorem compactModulusRealizerToEventFlow_injective
    {x y : CompactModulusRealizerUp} :
    compactModulusRealizerToEventFlow x = compactModulusRealizerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactModulusRealizerFromEventFlow (compactModulusRealizerToEventFlow x) =
        compactModulusRealizerFromEventFlow (compactModulusRealizerToEventFlow y) :=
    congrArg compactModulusRealizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactModulusRealizerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactModulusRealizerTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactModulusRealizerTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CompactModulusRealizerUp,
      compactModulusRealizerFields x = compactModulusRealizerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ G₁ Q₁ B₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ G₂ Q₂ B₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactModulusRealizerBHistCarrier : BHistCarrier CompactModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactModulusRealizerToEventFlow
  fromEventFlow := compactModulusRealizerFromEventFlow

instance compactModulusRealizerChapterTasteGate :
    ChapterTasteGate CompactModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactModulusRealizerFromEventFlow (compactModulusRealizerToEventFlow x) = some x
    exact CompactModulusRealizerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactModulusRealizerToEventFlow_injective heq)

instance compactModulusRealizerFieldFaithful :
    FieldFaithful CompactModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactModulusRealizerFields
  field_faithful := CompactModulusRealizerTasteGate_single_carrier_alignment_fields_faithful

instance compactModulusRealizerNontrivial : Nontrivial CompactModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactModulusRealizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactModulusRealizerUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CompactModulusRealizerTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CompactModulusRealizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactModulusRealizerChapterTasteGate

theorem CompactModulusRealizerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactModulusRealizerDecodeBHist (compactModulusRealizerEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactModulusRealizerUp) ∧
        Nonempty (ChapterTasteGate CompactModulusRealizerUp) ∧
          compactModulusRealizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨CompactModulusRealizerTasteGate_single_carrier_alignment_decode_encode,
      ⟨compactModulusRealizerBHistCarrier⟩,
      ⟨compactModulusRealizerChapterTasteGate⟩, rfl⟩

end BEDC.Derived.CompactModulusRealizerUp
