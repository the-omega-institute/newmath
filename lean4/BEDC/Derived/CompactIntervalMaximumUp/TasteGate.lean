import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalMaximumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalMaximumUp : Type where
  | mk (I F G N S R E W H C P L : BHist) : CompactIntervalMaximumUp
  deriving DecidableEq

def compactIntervalMaximumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalMaximumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalMaximumEncodeBHist h

def compactIntervalMaximumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalMaximumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalMaximumDecodeBHist tail)

private theorem compactIntervalMaximumDecodeEncode :
    ∀ h : BHist, compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactIntervalMaximumFields : CompactIntervalMaximumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalMaximumUp.mk I F G N S R E W H C P L =>
      [I, F, G, N, S, R, E, W, H, C, P, L]

def compactIntervalMaximumToEventFlow : CompactIntervalMaximumUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactIntervalMaximumFields x).map compactIntervalMaximumEncodeBHist

private def compactIntervalMaximumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactIntervalMaximumEventAtDefault index rest

def compactIntervalMaximumFromEventFlow (ef : EventFlow) : Option CompactIntervalMaximumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactIntervalMaximumUp.mk
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 0 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 1 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 2 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 3 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 4 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 5 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 6 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 7 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 8 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 9 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 10 ef))
      (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEventAtDefault 11 ef)))

private theorem compactIntervalMaximumRoundTrip :
    ∀ x : CompactIntervalMaximumUp,
      compactIntervalMaximumFromEventFlow (compactIntervalMaximumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F G N S R E W H C P L =>
      change
        some
          (CompactIntervalMaximumUp.mk
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist I))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist F))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist G))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist N))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist S))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist R))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist E))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist W))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist H))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist C))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist P))
            (compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist L))) =
          some (CompactIntervalMaximumUp.mk I F G N S R E W H C P L)
      rw [compactIntervalMaximumDecodeEncode I, compactIntervalMaximumDecodeEncode F,
        compactIntervalMaximumDecodeEncode G, compactIntervalMaximumDecodeEncode N,
        compactIntervalMaximumDecodeEncode S, compactIntervalMaximumDecodeEncode R,
        compactIntervalMaximumDecodeEncode E, compactIntervalMaximumDecodeEncode W,
        compactIntervalMaximumDecodeEncode H, compactIntervalMaximumDecodeEncode C,
        compactIntervalMaximumDecodeEncode P, compactIntervalMaximumDecodeEncode L]

private theorem compactIntervalMaximumToEventFlow_injective
    {x y : CompactIntervalMaximumUp} :
    compactIntervalMaximumToEventFlow x = compactIntervalMaximumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalMaximumFromEventFlow (compactIntervalMaximumToEventFlow x) =
        compactIntervalMaximumFromEventFlow (compactIntervalMaximumToEventFlow y) :=
    congrArg compactIntervalMaximumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactIntervalMaximumRoundTrip x).symm
      (Eq.trans hread (compactIntervalMaximumRoundTrip y)))

private theorem compactIntervalMaximumFieldFaithful :
    ∀ x y : CompactIntervalMaximumUp,
      compactIntervalMaximumFields x = compactIntervalMaximumFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ F₁ G₁ N₁ S₁ R₁ E₁ W₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk I₂ F₂ G₂ N₂ S₂ R₂ E₂ W₂ H₂ C₂ P₂ L₂ =>
          cases hfields
          rfl

instance compactIntervalMaximumBHistCarrier : BHistCarrier CompactIntervalMaximumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalMaximumToEventFlow
  fromEventFlow := compactIntervalMaximumFromEventFlow

instance compactIntervalMaximumChapterTasteGate : ChapterTasteGate CompactIntervalMaximumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactIntervalMaximumFromEventFlow (compactIntervalMaximumToEventFlow x) = some x
    exact compactIntervalMaximumRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactIntervalMaximumToEventFlow_injective heq)

instance compactIntervalMaximumFieldFaithfulInst : FieldFaithful CompactIntervalMaximumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactIntervalMaximumFields
  field_faithful := compactIntervalMaximumFieldFaithful

instance compactIntervalMaximumNontrivial : BEDC.Meta.TasteGate.Nontrivial CompactIntervalMaximumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactIntervalMaximumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompactIntervalMaximumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactIntervalMaximumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactIntervalMaximumChapterTasteGate

theorem CompactIntervalMaximumTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactIntervalMaximumDecodeBHist (compactIntervalMaximumEncodeBHist h) = h) ∧
      (∀ x : CompactIntervalMaximumUp,
        compactIntervalMaximumFromEventFlow (compactIntervalMaximumToEventFlow x) = some x) ∧
        (∀ x y : CompactIntervalMaximumUp,
          compactIntervalMaximumToEventFlow x = compactIntervalMaximumToEventFlow y → x = y) ∧
          compactIntervalMaximumEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact compactIntervalMaximumDecodeEncode
  constructor
  · exact compactIntervalMaximumRoundTrip
  constructor
  · intro x y heq
    exact compactIntervalMaximumToEventFlow_injective heq
  · rfl

end BEDC.Derived.CompactIntervalMaximumUp
