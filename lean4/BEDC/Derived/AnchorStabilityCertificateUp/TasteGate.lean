import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AnchorStabilityCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AnchorStabilityCertificateUp : Type where
  | mk :
      (family invariant route classifier ledger transport continuation provenance name : BHist) →
        AnchorStabilityCertificateUp
  deriving DecidableEq

def anchorStabilityCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: anchorStabilityCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: anchorStabilityCertificateEncodeBHist h

def anchorStabilityCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (anchorStabilityCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (anchorStabilityCertificateDecodeBHist tail)

private theorem anchorStabilityCertificateDecode_encode :
    ∀ h : BHist,
      anchorStabilityCertificateDecodeBHist
          (anchorStabilityCertificateEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def anchorStabilityCertificateFields :
    AnchorStabilityCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AnchorStabilityCertificateUp.mk F I R K L H C P N =>
      [F, I, R, K, L, H, C, P, N]

def anchorStabilityCertificateToEventFlow :
    AnchorStabilityCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AnchorStabilityCertificateUp.mk F I R K L H C P N =>
      [[BMark.b0],
        anchorStabilityCertificateEncodeBHist F,
        [BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        anchorStabilityCertificateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        anchorStabilityCertificateEncodeBHist N]

private def anchorStabilityCertificateEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      anchorStabilityCertificateEventAtDefault index rest

def anchorStabilityCertificateFromEventFlow
    (ef : EventFlow) : Option AnchorStabilityCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AnchorStabilityCertificateUp.mk
      (anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEventAtDefault 1 ef))
      (anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEventAtDefault 3 ef))
      (anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEventAtDefault 5 ef))
      (anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEventAtDefault 7 ef))
      (anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEventAtDefault 9 ef))
      (anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEventAtDefault 11 ef))
      (anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEventAtDefault 13 ef))
      (anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEventAtDefault 15 ef))
      (anchorStabilityCertificateDecodeBHist
        (anchorStabilityCertificateEventAtDefault 17 ef)))

private theorem anchorStabilityCertificate_round_trip :
    ∀ x : AnchorStabilityCertificateUp,
      anchorStabilityCertificateFromEventFlow
          (anchorStabilityCertificateToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F I R K L H C P N =>
      change
        some
          (AnchorStabilityCertificateUp.mk
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist F))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist I))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist R))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist K))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist L))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist H))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist C))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist P))
            (anchorStabilityCertificateDecodeBHist
              (anchorStabilityCertificateEncodeBHist N))) =
          some (AnchorStabilityCertificateUp.mk F I R K L H C P N)
      rw [anchorStabilityCertificateDecode_encode F,
        anchorStabilityCertificateDecode_encode I,
        anchorStabilityCertificateDecode_encode R,
        anchorStabilityCertificateDecode_encode K,
        anchorStabilityCertificateDecode_encode L,
        anchorStabilityCertificateDecode_encode H,
        anchorStabilityCertificateDecode_encode C,
        anchorStabilityCertificateDecode_encode P,
        anchorStabilityCertificateDecode_encode N]

private theorem anchorStabilityCertificateToEventFlow_injective
    {x y : AnchorStabilityCertificateUp} :
    anchorStabilityCertificateToEventFlow x =
      anchorStabilityCertificateToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      anchorStabilityCertificateFromEventFlow
          (anchorStabilityCertificateToEventFlow x) =
        anchorStabilityCertificateFromEventFlow
          (anchorStabilityCertificateToEventFlow y) :=
    congrArg anchorStabilityCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (anchorStabilityCertificate_round_trip x).symm
      (Eq.trans hread (anchorStabilityCertificate_round_trip y)))

private theorem anchorStabilityCertificate_fields_faithful :
    ∀ x y : AnchorStabilityCertificateUp,
      anchorStabilityCertificateFields x =
        anchorStabilityCertificateFields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ I₁ R₁ K₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ I₂ R₂ K₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance anchorStabilityCertificateBHistCarrier :
    BHistCarrier AnchorStabilityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := anchorStabilityCertificateToEventFlow
  fromEventFlow := anchorStabilityCertificateFromEventFlow

instance anchorStabilityCertificateChapterTasteGate :
    ChapterTasteGate AnchorStabilityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      anchorStabilityCertificateFromEventFlow
          (anchorStabilityCertificateToEventFlow x) =
        some x
    exact anchorStabilityCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (anchorStabilityCertificateToEventFlow_injective heq)

instance anchorStabilityCertificateFieldFaithful :
    FieldFaithful AnchorStabilityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := anchorStabilityCertificateFields
  field_faithful := anchorStabilityCertificate_fields_faithful

instance anchorStabilityCertificateNontrivial :
    Nontrivial AnchorStabilityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AnchorStabilityCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AnchorStabilityCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AnchorStabilityCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  anchorStabilityCertificateChapterTasteGate

end BEDC.Derived.AnchorStabilityCertificateUp
