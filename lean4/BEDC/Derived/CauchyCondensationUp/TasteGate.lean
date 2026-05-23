import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCondensationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCondensationUp : Type where
  | mk (S W B L T R E H C P N : BHist) : CauchyCondensationUp
  deriving DecidableEq

def cauchyCondensationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCondensationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCondensationEncodeBHist h

def cauchyCondensationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCondensationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCondensationDecodeBHist tail)

private theorem cauchyCondensationDecodeEncode :
    ∀ h : BHist, cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCondensationFields : CauchyCondensationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCondensationUp.mk S W B L T R E H C P N => [S, W, B, L, T, R, E, H, C, P, N]

def cauchyCondensationToEventFlow : CauchyCondensationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCondensationFields x).map cauchyCondensationEncodeBHist

private def cauchyCondensationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCondensationEventAt index rest

def cauchyCondensationFromEventFlow (ef : EventFlow) : Option CauchyCondensationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCondensationUp.mk
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 0 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 1 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 2 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 3 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 4 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 5 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 6 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 7 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 8 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 9 ef))
      (cauchyCondensationDecodeBHist (cauchyCondensationEventAt 10 ef)))

private theorem cauchyCondensationRoundTrip (x : CauchyCondensationUp) :
    cauchyCondensationFromEventFlow (cauchyCondensationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W B L T R E H C P N =>
      change
        some
          (CauchyCondensationUp.mk
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist S))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist W))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist B))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist L))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist T))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist R))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist E))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist H))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist C))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist P))
            (cauchyCondensationDecodeBHist (cauchyCondensationEncodeBHist N))) =
          some (CauchyCondensationUp.mk S W B L T R E H C P N)
      rw [cauchyCondensationDecodeEncode S, cauchyCondensationDecodeEncode W,
        cauchyCondensationDecodeEncode B, cauchyCondensationDecodeEncode L,
        cauchyCondensationDecodeEncode T, cauchyCondensationDecodeEncode R,
        cauchyCondensationDecodeEncode E, cauchyCondensationDecodeEncode H,
        cauchyCondensationDecodeEncode C, cauchyCondensationDecodeEncode P,
        cauchyCondensationDecodeEncode N]

private theorem cauchyCondensationToEventFlow_injective {x y : CauchyCondensationUp} :
    cauchyCondensationToEventFlow x = cauchyCondensationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCondensationFromEventFlow (cauchyCondensationToEventFlow x) =
        cauchyCondensationFromEventFlow (cauchyCondensationToEventFlow y) :=
    congrArg cauchyCondensationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCondensationRoundTrip x).symm
      (Eq.trans hread (cauchyCondensationRoundTrip y)))

private theorem cauchyCondensationFieldFaithful :
    ∀ x y : CauchyCondensationUp, cauchyCondensationFields x = cauchyCondensationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ W₁ B₁ L₁ T₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ W₂ B₂ L₂ T₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyCondensationBHistCarrier : BHistCarrier CauchyCondensationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCondensationToEventFlow
  fromEventFlow := cauchyCondensationFromEventFlow

instance cauchyCondensationChapterTasteGate : ChapterTasteGate CauchyCondensationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCondensationFromEventFlow (cauchyCondensationToEventFlow x) = some x
    exact cauchyCondensationRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCondensationToEventFlow_injective heq)

instance cauchyCondensationFieldFaithfulInstance : FieldFaithful CauchyCondensationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCondensationFields
  field_faithful := cauchyCondensationFieldFaithful

instance cauchyCondensationNontrivial : Nontrivial CauchyCondensationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCondensationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCondensationUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyCondensationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyCondensationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCondensationChapterTasteGate

theorem CauchyCondensationTasteGate_single_carrier_alignment :
    (∀ x : CauchyCondensationUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      cauchyCondensationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro x
    exact ChapterTasteGate.round_trip x
  · rfl

end BEDC.Derived.CauchyCondensationUp
