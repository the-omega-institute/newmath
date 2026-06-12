import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AsymptoticEquicontinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AsymptoticEquicontinuityUp : Type where
  | mk (K F E U T S R H C P N : BHist) : AsymptoticEquicontinuityUp
  deriving DecidableEq

def asymptoticEquicontinuityEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: asymptoticEquicontinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: asymptoticEquicontinuityEncodeBHist h

def asymptoticEquicontinuityDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (asymptoticEquicontinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (asymptoticEquicontinuityDecodeBHist tail)

private theorem AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, asymptoticEquicontinuityDecodeBHist
      (asymptoticEquicontinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def asymptoticEquicontinuityFields :
    AsymptoticEquicontinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AsymptoticEquicontinuityUp.mk K F E U T S R H C P N =>
      [K, F, E, U, T, S, R, H, C, P, N]

def asymptoticEquicontinuityToEventFlow :
    AsymptoticEquicontinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (asymptoticEquicontinuityFields x).map asymptoticEquicontinuityEncodeBHist

private def asymptoticEquicontinuityEventAtDefault :
    Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      asymptoticEquicontinuityEventAtDefault index rest

def asymptoticEquicontinuityFromEventFlow
    (ef : EventFlow) : Option AsymptoticEquicontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AsymptoticEquicontinuityUp.mk
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 0 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 1 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 2 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 3 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 4 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 5 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 6 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 7 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 8 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 9 ef))
      (asymptoticEquicontinuityDecodeBHist
        (asymptoticEquicontinuityEventAtDefault 10 ef)))

private theorem
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_event_readback
    (K F E U T S R H C P N : BHist) :
    asymptoticEquicontinuityFromEventFlow
    [asymptoticEquicontinuityEncodeBHist K,
          asymptoticEquicontinuityEncodeBHist F,
          asymptoticEquicontinuityEncodeBHist E,
          asymptoticEquicontinuityEncodeBHist U,
          asymptoticEquicontinuityEncodeBHist T,
          asymptoticEquicontinuityEncodeBHist S,
          asymptoticEquicontinuityEncodeBHist R,
          asymptoticEquicontinuityEncodeBHist H,
          asymptoticEquicontinuityEncodeBHist C,
          asymptoticEquicontinuityEncodeBHist P,
          asymptoticEquicontinuityEncodeBHist N] =
      some (AsymptoticEquicontinuityUp.mk K F E U T S R H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  change
    some
      (AsymptoticEquicontinuityUp.mk
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist K))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist F))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist E))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist U))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist T))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist S))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist R))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist H))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist C))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist P))
        (asymptoticEquicontinuityDecodeBHist
          (asymptoticEquicontinuityEncodeBHist N))) =
      some (AsymptoticEquicontinuityUp.mk K F E U T S R H C P N)
  rw [AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode K,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode F,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode E,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode U,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode T,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode S,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode R,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode H,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode C,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode P,
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode N]

private theorem AsymptoticEquicontinuityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AsymptoticEquicontinuityUp,
      asymptoticEquicontinuityFromEventFlow
          (asymptoticEquicontinuityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F E U T S R H C P N =>
      exact AsymptoticEquicontinuityTasteGate_single_carrier_alignment_event_readback
        K F E U T S R H C P N

private theorem AsymptoticEquicontinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AsymptoticEquicontinuityUp} :
    asymptoticEquicontinuityToEventFlow x =
        asymptoticEquicontinuityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      asymptoticEquicontinuityFromEventFlow
          (asymptoticEquicontinuityToEventFlow x) =
        asymptoticEquicontinuityFromEventFlow
          (asymptoticEquicontinuityToEventFlow y) :=
    congrArg asymptoticEquicontinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AsymptoticEquicontinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AsymptoticEquicontinuityTasteGate_single_carrier_alignment_round_trip y)))

private theorem
    AsymptoticEquicontinuityTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AsymptoticEquicontinuityUp,
      asymptoticEquicontinuityFields x = asymptoticEquicontinuityFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ E₁ U₁ T₁ S₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ E₂ U₂ T₂ S₂ R₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hK tail0
          injection tail0 with hF tail1
          injection tail1 with hE tail2
          injection tail2 with hU tail3
          injection tail3 with hT tail4
          injection tail4 with hS tail5
          injection tail5 with hR tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hK
          subst hF
          subst hE
          subst hU
          subst hT
          subst hS
          subst hR
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance asymptoticEquicontinuityBHistCarrier :
    BHistCarrier AsymptoticEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := asymptoticEquicontinuityToEventFlow
  fromEventFlow := asymptoticEquicontinuityFromEventFlow

instance asymptoticEquicontinuityChapterTasteGate :
    ChapterTasteGate AsymptoticEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      asymptoticEquicontinuityFromEventFlow
          (asymptoticEquicontinuityToEventFlow x) =
        some x
    exact AsymptoticEquicontinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (AsymptoticEquicontinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance asymptoticEquicontinuityFieldFaithful :
    FieldFaithful AsymptoticEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := asymptoticEquicontinuityFields
  field_faithful := AsymptoticEquicontinuityTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate AsymptoticEquicontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  asymptoticEquicontinuityChapterTasteGate

def taste_gate_witness : FieldFaithful AsymptoticEquicontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  asymptoticEquicontinuityFieldFaithful

theorem AsymptoticEquicontinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      asymptoticEquicontinuityDecodeBHist (asymptoticEquicontinuityEncodeBHist h) = h) ∧
      (∀ x : AsymptoticEquicontinuityUp,
        asymptoticEquicontinuityFromEventFlow
            (asymptoticEquicontinuityToEventFlow x) =
          some x) ∧
        (∀ x y : AsymptoticEquicontinuityUp,
          asymptoticEquicontinuityToEventFlow x =
              asymptoticEquicontinuityToEventFlow y →
            x = y) ∧
          asymptoticEquicontinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨AsymptoticEquicontinuityTasteGate_single_carrier_alignment_decode_encode,
      AsymptoticEquicontinuityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        AsymptoticEquicontinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AsymptoticEquicontinuityUp
