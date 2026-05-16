import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AnchorChangeInvariantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AnchorChangeInvariantUp : Type where
  | mk (H A I S R L T P N : BHist) : AnchorChangeInvariantUp
  deriving DecidableEq

def anchorChangeInvariantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: anchorChangeInvariantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: anchorChangeInvariantEncodeBHist h

def anchorChangeInvariantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (anchorChangeInvariantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (anchorChangeInvariantDecodeBHist tail)

private theorem anchorChangeInvariantDecodeEncodeBHist :
    ∀ h : BHist,
      anchorChangeInvariantDecodeBHist
        (anchorChangeInvariantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def anchorChangeInvariantFields : AnchorChangeInvariantUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AnchorChangeInvariantUp.mk H A I S R L T P N => [H, A, I, S, R, L, T, P, N]

def anchorChangeInvariantToEventFlow : AnchorChangeInvariantUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (anchorChangeInvariantFields x).map anchorChangeInvariantEncodeBHist

def anchorChangeInvariantFromEventFlow :
    EventFlow → Option AnchorChangeInvariantUp
  -- BEDC touchpoint anchor: BHist BMark
  | H :: A :: I :: S :: R :: L :: T :: P :: N :: [] =>
      some
        (AnchorChangeInvariantUp.mk
          (anchorChangeInvariantDecodeBHist H)
          (anchorChangeInvariantDecodeBHist A)
          (anchorChangeInvariantDecodeBHist I)
          (anchorChangeInvariantDecodeBHist S)
          (anchorChangeInvariantDecodeBHist R)
          (anchorChangeInvariantDecodeBHist L)
          (anchorChangeInvariantDecodeBHist T)
          (anchorChangeInvariantDecodeBHist P)
          (anchorChangeInvariantDecodeBHist N))
  | _ => none

private theorem anchorChangeInvariant_round_trip :
    ∀ x : AnchorChangeInvariantUp,
      anchorChangeInvariantFromEventFlow
        (anchorChangeInvariantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H A I S R L T P N =>
      change
        some
          (AnchorChangeInvariantUp.mk
            (anchorChangeInvariantDecodeBHist (anchorChangeInvariantEncodeBHist H))
            (anchorChangeInvariantDecodeBHist (anchorChangeInvariantEncodeBHist A))
            (anchorChangeInvariantDecodeBHist (anchorChangeInvariantEncodeBHist I))
            (anchorChangeInvariantDecodeBHist (anchorChangeInvariantEncodeBHist S))
            (anchorChangeInvariantDecodeBHist (anchorChangeInvariantEncodeBHist R))
            (anchorChangeInvariantDecodeBHist (anchorChangeInvariantEncodeBHist L))
            (anchorChangeInvariantDecodeBHist (anchorChangeInvariantEncodeBHist T))
            (anchorChangeInvariantDecodeBHist (anchorChangeInvariantEncodeBHist P))
            (anchorChangeInvariantDecodeBHist (anchorChangeInvariantEncodeBHist N))) =
          some (AnchorChangeInvariantUp.mk H A I S R L T P N)
      rw [anchorChangeInvariantDecodeEncodeBHist H,
        anchorChangeInvariantDecodeEncodeBHist A,
        anchorChangeInvariantDecodeEncodeBHist I,
        anchorChangeInvariantDecodeEncodeBHist S,
        anchorChangeInvariantDecodeEncodeBHist R,
        anchorChangeInvariantDecodeEncodeBHist L,
        anchorChangeInvariantDecodeEncodeBHist T,
        anchorChangeInvariantDecodeEncodeBHist P,
        anchorChangeInvariantDecodeEncodeBHist N]

private theorem anchorChangeInvariantToEventFlow_injective
    {x y : AnchorChangeInvariantUp} :
    anchorChangeInvariantToEventFlow x =
      anchorChangeInvariantToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      anchorChangeInvariantFromEventFlow (anchorChangeInvariantToEventFlow x) =
        anchorChangeInvariantFromEventFlow (anchorChangeInvariantToEventFlow y) :=
    congrArg anchorChangeInvariantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (anchorChangeInvariant_round_trip x).symm
      (Eq.trans hread (anchorChangeInvariant_round_trip y)))

private theorem anchorChangeInvariant_fields_faithful :
    ∀ x y : AnchorChangeInvariantUp,
      anchorChangeInvariantFields x = anchorChangeInvariantFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ A₁ I₁ S₁ R₁ L₁ T₁ P₁ N₁ =>
      cases y with
      | mk H₂ A₂ I₂ S₂ R₂ L₂ T₂ P₂ N₂ =>
          injection hfields with hH t0
          injection t0 with hA t1
          injection t1 with hI t2
          injection t2 with hS t3
          injection t3 with hR t4
          injection t4 with hL t5
          injection t5 with hT t6
          injection t6 with hP t7
          injection t7 with hN _
          subst hH
          subst hA
          subst hI
          subst hS
          subst hR
          subst hL
          subst hT
          subst hP
          subst hN
          rfl

instance anchorChangeInvariantBHistCarrier :
    BHistCarrier AnchorChangeInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := anchorChangeInvariantToEventFlow
  fromEventFlow := anchorChangeInvariantFromEventFlow

instance anchorChangeInvariantChapterTasteGate :
    ChapterTasteGate AnchorChangeInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      anchorChangeInvariantFromEventFlow
        (anchorChangeInvariantToEventFlow x) = some x
    exact anchorChangeInvariant_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (anchorChangeInvariantToEventFlow_injective heq)

instance anchorChangeInvariantFieldFaithful :
    FieldFaithful AnchorChangeInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := anchorChangeInvariantFields
  field_faithful := anchorChangeInvariant_fields_faithful

instance anchorChangeInvariantNontrivial :
    Nontrivial AnchorChangeInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AnchorChangeInvariantUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AnchorChangeInvariantUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AnchorChangeInvariantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  anchorChangeInvariantChapterTasteGate

end BEDC.Derived.AnchorChangeInvariantUp
