import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractionMappingTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractionMappingTheoremUp : Type where
  | mk (M D K S E U Q H C P N : BHist) : ContractionMappingTheoremUp
  deriving DecidableEq

def contractionMappingTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contractionMappingTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contractionMappingTheoremEncodeBHist h

def contractionMappingTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contractionMappingTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contractionMappingTheoremDecodeBHist tail)

private theorem contractionMappingTheoremDecodeEncode :
    ∀ h : BHist,
      contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contractionMappingTheoremFields : ContractionMappingTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractionMappingTheoremUp.mk M D K S E U Q H C P N =>
      [M, D, K, S, E, U, Q, H, C, P, N]

def contractionMappingTheoremToEventFlow : ContractionMappingTheoremUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (contractionMappingTheoremFields x).map contractionMappingTheoremEncodeBHist

private def contractionMappingTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => contractionMappingTheoremEventAtDefault index rest

def contractionMappingTheoremFromEventFlow
    (ef : EventFlow) : Option ContractionMappingTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContractionMappingTheoremUp.mk
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 0 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 1 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 2 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 3 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 4 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 5 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 6 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 7 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 8 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 9 ef))
      (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEventAtDefault 10 ef)))

private theorem contractionMappingTheoremRoundTrip :
    ∀ x : ContractionMappingTheoremUp,
      contractionMappingTheoremFromEventFlow (contractionMappingTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D K S E U Q H C P N =>
      change
        some
          (ContractionMappingTheoremUp.mk
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist M))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist D))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist K))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist S))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist E))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist U))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist Q))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist H))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist C))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist P))
            (contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist N))) =
          some (ContractionMappingTheoremUp.mk M D K S E U Q H C P N)
      rw [contractionMappingTheoremDecodeEncode M, contractionMappingTheoremDecodeEncode D,
        contractionMappingTheoremDecodeEncode K, contractionMappingTheoremDecodeEncode S,
        contractionMappingTheoremDecodeEncode E, contractionMappingTheoremDecodeEncode U,
        contractionMappingTheoremDecodeEncode Q, contractionMappingTheoremDecodeEncode H,
        contractionMappingTheoremDecodeEncode C, contractionMappingTheoremDecodeEncode P,
        contractionMappingTheoremDecodeEncode N]

private theorem contractionMappingTheoremToEventFlow_injective
    {x y : ContractionMappingTheoremUp} :
    contractionMappingTheoremToEventFlow x = contractionMappingTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractionMappingTheoremFromEventFlow (contractionMappingTheoremToEventFlow x) =
        contractionMappingTheoremFromEventFlow (contractionMappingTheoremToEventFlow y) :=
    congrArg contractionMappingTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (contractionMappingTheoremRoundTrip x).symm
      (Eq.trans hread (contractionMappingTheoremRoundTrip y)))

private theorem contractionMappingTheoremFieldFaithful :
    ∀ x y : ContractionMappingTheoremUp,
      contractionMappingTheoremFields x = contractionMappingTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ D₁ K₁ S₁ E₁ U₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ D₂ K₂ S₂ E₂ U₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance contractionMappingTheoremBHistCarrier :
    BHistCarrier ContractionMappingTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractionMappingTheoremToEventFlow
  fromEventFlow := contractionMappingTheoremFromEventFlow

instance contractionMappingTheoremChapterTasteGate :
    ChapterTasteGate ContractionMappingTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contractionMappingTheoremFromEventFlow (contractionMappingTheoremToEventFlow x) = some x
    exact contractionMappingTheoremRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (contractionMappingTheoremToEventFlow_injective heq)

instance contractionMappingTheoremFieldFaithfulInst :
    FieldFaithful ContractionMappingTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := contractionMappingTheoremFields
  field_faithful := contractionMappingTheoremFieldFaithful

instance contractionMappingTheoremNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ContractionMappingTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContractionMappingTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContractionMappingTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ContractionMappingTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contractionMappingTheoremChapterTasteGate

theorem ContractionMappingTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      contractionMappingTheoremDecodeBHist (contractionMappingTheoremEncodeBHist h) = h) ∧
      (∀ x : ContractionMappingTheoremUp,
        contractionMappingTheoremFromEventFlow (contractionMappingTheoremToEventFlow x) =
          some x) ∧
        (∀ x y : ContractionMappingTheoremUp,
          contractionMappingTheoremToEventFlow x = contractionMappingTheoremToEventFlow y →
            x = y) ∧
          contractionMappingTheoremEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact contractionMappingTheoremDecodeEncode
  constructor
  · exact contractionMappingTheoremRoundTrip
  constructor
  · intro x y heq
    exact contractionMappingTheoremToEventFlow_injective heq
  · rfl

end BEDC.Derived.ContractionMappingTheoremUp
