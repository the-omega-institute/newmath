import BEDC.Derived.SamuelCompletionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SamuelCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def samuelCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: samuelCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: samuelCompletionEncodeBHist h

def samuelCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (samuelCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (samuelCompletionDecodeBHist tail)

private theorem SamuelCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, samuelCompletionDecodeBHist (samuelCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def samuelCompletionFields : SamuelCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SamuelCompletionUp.mk uniformEntourage cauchyFilter denseUniformEmbedding streamWindow
      regularReadback realSeal transport replay provenance name =>
      [uniformEntourage, cauchyFilter, denseUniformEmbedding, streamWindow, regularReadback,
        realSeal, transport, replay, provenance, name]

def samuelCompletionToEventFlow : SamuelCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (samuelCompletionFields x).map samuelCompletionEncodeBHist

private def samuelCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => samuelCompletionEventAtDefault index rest

def samuelCompletionFromEventFlow (ef : EventFlow) : Option SamuelCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SamuelCompletionUp.mk
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 0 ef))
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 1 ef))
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 2 ef))
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 3 ef))
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 4 ef))
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 5 ef))
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 6 ef))
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 7 ef))
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 8 ef))
      (samuelCompletionDecodeBHist (samuelCompletionEventAtDefault 9 ef)))

private theorem SamuelCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SamuelCompletionUp,
      samuelCompletionFromEventFlow (samuelCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk uniformEntourage cauchyFilter denseUniformEmbedding streamWindow regularReadback
      realSeal transport replay provenance name =>
      change
        some
          (SamuelCompletionUp.mk
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist uniformEntourage))
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist cauchyFilter))
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist denseUniformEmbedding))
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist streamWindow))
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist regularReadback))
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist realSeal))
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist transport))
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist replay))
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist provenance))
            (samuelCompletionDecodeBHist (samuelCompletionEncodeBHist name))) =
          some
            (SamuelCompletionUp.mk uniformEntourage cauchyFilter denseUniformEmbedding
              streamWindow regularReadback realSeal transport replay provenance name)
      rw [SamuelCompletionTasteGate_single_carrier_alignment_decode uniformEntourage,
        SamuelCompletionTasteGate_single_carrier_alignment_decode cauchyFilter,
        SamuelCompletionTasteGate_single_carrier_alignment_decode denseUniformEmbedding,
        SamuelCompletionTasteGate_single_carrier_alignment_decode streamWindow,
        SamuelCompletionTasteGate_single_carrier_alignment_decode regularReadback,
        SamuelCompletionTasteGate_single_carrier_alignment_decode realSeal,
        SamuelCompletionTasteGate_single_carrier_alignment_decode transport,
        SamuelCompletionTasteGate_single_carrier_alignment_decode replay,
        SamuelCompletionTasteGate_single_carrier_alignment_decode provenance,
        SamuelCompletionTasteGate_single_carrier_alignment_decode name]

private theorem SamuelCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SamuelCompletionUp} :
    samuelCompletionToEventFlow x = samuelCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      samuelCompletionFromEventFlow (samuelCompletionToEventFlow x) =
        samuelCompletionFromEventFlow (samuelCompletionToEventFlow y) :=
    congrArg samuelCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SamuelCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SamuelCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem SamuelCompletionTasteGate_single_carrier_alignment_fields :
    ∀ x y : SamuelCompletionUp, samuelCompletionFields x = samuelCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk uniformEntourage₁ cauchyFilter₁ denseUniformEmbedding₁ streamWindow₁
      regularReadback₁ realSeal₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk uniformEntourage₂ cauchyFilter₂ denseUniformEmbedding₂ streamWindow₂
          regularReadback₂ realSeal₂ transport₂ replay₂ provenance₂ name₂ =>
          injection hfields with hUniformEntourage tail0
          injection tail0 with hCauchyFilter tail1
          injection tail1 with hDenseUniformEmbedding tail2
          injection tail2 with hStreamWindow tail3
          injection tail3 with hRegularReadback tail4
          injection tail4 with hRealSeal tail5
          injection tail5 with hTransport tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hName _
          subst hUniformEntourage
          subst hCauchyFilter
          subst hDenseUniformEmbedding
          subst hStreamWindow
          subst hRegularReadback
          subst hRealSeal
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hName
          rfl

instance samuelCompletionBHistCarrier : BHistCarrier SamuelCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := samuelCompletionToEventFlow
  fromEventFlow := samuelCompletionFromEventFlow

instance samuelCompletionChapterTasteGate : ChapterTasteGate SamuelCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change samuelCompletionFromEventFlow (samuelCompletionToEventFlow x) = some x
    exact SamuelCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SamuelCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance samuelCompletionFieldFaithful : FieldFaithful SamuelCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := samuelCompletionFields
  field_faithful := SamuelCompletionTasteGate_single_carrier_alignment_fields

instance samuelCompletionNontrivial : Nontrivial SamuelCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SamuelCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SamuelCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SamuelCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  samuelCompletionChapterTasteGate

theorem SamuelCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, samuelCompletionDecodeBHist (samuelCompletionEncodeBHist h) = h) ∧
      (∀ x : SamuelCompletionUp,
        samuelCompletionFromEventFlow (samuelCompletionToEventFlow x) = some x) ∧
        (∀ x y : SamuelCompletionUp,
          samuelCompletionToEventFlow x = samuelCompletionToEventFlow y → x = y) ∧
          samuelCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SamuelCompletionTasteGate_single_carrier_alignment_decode,
      SamuelCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SamuelCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SamuelCompletionUp
