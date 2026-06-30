import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionRouteUp : Type where
  | mk (D S Q E B T C P N : BHist) : CauchyCompletionRouteUp
  deriving DecidableEq

def cauchyCompletionRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionRouteEncodeBHist h

def cauchyCompletionRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionRouteDecodeBHist tail)

private theorem CauchyCompletionRouteTasteGate_decode_encode :
    ∀ h : BHist,
      cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionRouteFields : CauchyCompletionRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionRouteUp.mk D S Q E B T C P N => [D, S, Q, E, B, T, C, P, N]

def cauchyCompletionRouteToEventFlow : CauchyCompletionRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionRouteFields x).map cauchyCompletionRouteEncodeBHist

private def cauchyCompletionRouteEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionRouteEventAtDefault index rest

def cauchyCompletionRouteFromEventFlow : EventFlow → Option CauchyCompletionRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (CauchyCompletionRouteUp.mk
          (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEventAtDefault 0 flow))
          (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEventAtDefault 1 flow))
          (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEventAtDefault 2 flow))
          (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEventAtDefault 3 flow))
          (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEventAtDefault 4 flow))
          (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEventAtDefault 5 flow))
          (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEventAtDefault 6 flow))
          (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEventAtDefault 7 flow))
          (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEventAtDefault 8 flow)))

private theorem CauchyCompletionRouteTasteGate_round_trip
    (x : CauchyCompletionRouteUp) :
    cauchyCompletionRouteFromEventFlow (cauchyCompletionRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S Q E B T C P N =>
      change
        some
          (CauchyCompletionRouteUp.mk
            (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist D))
            (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist S))
            (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist Q))
            (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist E))
            (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist B))
            (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist T))
            (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist C))
            (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist P))
            (cauchyCompletionRouteDecodeBHist (cauchyCompletionRouteEncodeBHist N))) =
          some (CauchyCompletionRouteUp.mk D S Q E B T C P N)
      rw [CauchyCompletionRouteTasteGate_decode_encode D,
        CauchyCompletionRouteTasteGate_decode_encode S,
        CauchyCompletionRouteTasteGate_decode_encode Q,
        CauchyCompletionRouteTasteGate_decode_encode E,
        CauchyCompletionRouteTasteGate_decode_encode B,
        CauchyCompletionRouteTasteGate_decode_encode T,
        CauchyCompletionRouteTasteGate_decode_encode C,
        CauchyCompletionRouteTasteGate_decode_encode P,
        CauchyCompletionRouteTasteGate_decode_encode N]

private theorem CauchyCompletionRouteTasteGate_toEventFlow_injective
    {x y : CauchyCompletionRouteUp} :
    cauchyCompletionRouteToEventFlow x = cauchyCompletionRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionRouteFromEventFlow (cauchyCompletionRouteToEventFlow x) =
        cauchyCompletionRouteFromEventFlow (cauchyCompletionRouteToEventFlow y) :=
    congrArg cauchyCompletionRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionRouteTasteGate_round_trip x).symm
      (Eq.trans hread (CauchyCompletionRouteTasteGate_round_trip y)))

private theorem CauchyCompletionRouteTasteGate_fields_faithful :
    ∀ x y : CauchyCompletionRouteUp,
      cauchyCompletionRouteFields x = cauchyCompletionRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ S₁ Q₁ E₁ B₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ S₂ Q₂ E₂ B₂ T₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyCompletionRouteBHistCarrier : BHistCarrier CauchyCompletionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionRouteToEventFlow
  fromEventFlow := cauchyCompletionRouteFromEventFlow

instance cauchyCompletionRouteChapterTasteGate :
    ChapterTasteGate CauchyCompletionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompletionRouteFromEventFlow (cauchyCompletionRouteToEventFlow x) = some x
    exact CauchyCompletionRouteTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionRouteTasteGate_toEventFlow_injective heq)

instance cauchyCompletionRouteFieldFaithful : FieldFaithful CauchyCompletionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionRouteFields
  field_faithful := CauchyCompletionRouteTasteGate_fields_faithful

theorem CauchyCompletionRouteTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchyCompletionRouteDecodeBHist
        (cauchyCompletionRouteEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionRouteUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionRouteUp) ∧
          cauchyCompletionRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact CauchyCompletionRouteTasteGate_decode_encode
  · constructor
    · exact ⟨cauchyCompletionRouteBHistCarrier⟩
    · constructor
      · exact ⟨cauchyCompletionRouteChapterTasteGate⟩
      · rfl

end BEDC.Derived.CauchyCompletionRouteUp
