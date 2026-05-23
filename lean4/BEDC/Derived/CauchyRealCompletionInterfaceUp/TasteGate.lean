import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRealCompletionInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRealCompletionInterfaceUp : Type where
  | mk (D S R B T H C P N : BHist) : CauchyRealCompletionInterfaceUp
  deriving DecidableEq

def cauchyRealCompletionInterfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRealCompletionInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRealCompletionInterfaceEncodeBHist h

def cauchyRealCompletionInterfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRealCompletionInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRealCompletionInterfaceDecodeBHist tail)

private theorem CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRealCompletionInterfaceFields :
    CauchyRealCompletionInterfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRealCompletionInterfaceUp.mk D S R B T H C P N => [D, S, R, B, T, H, C, P, N]

def cauchyRealCompletionInterfaceToEventFlow :
    CauchyRealCompletionInterfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRealCompletionInterfaceFields x).map cauchyRealCompletionInterfaceEncodeBHist

private def cauchyRealCompletionInterfaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRealCompletionInterfaceEventAt index rest

def cauchyRealCompletionInterfaceFromEventFlow (ef : EventFlow) :
    Option CauchyRealCompletionInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRealCompletionInterfaceUp.mk
      (cauchyRealCompletionInterfaceDecodeBHist (cauchyRealCompletionInterfaceEventAt 0 ef))
      (cauchyRealCompletionInterfaceDecodeBHist (cauchyRealCompletionInterfaceEventAt 1 ef))
      (cauchyRealCompletionInterfaceDecodeBHist (cauchyRealCompletionInterfaceEventAt 2 ef))
      (cauchyRealCompletionInterfaceDecodeBHist (cauchyRealCompletionInterfaceEventAt 3 ef))
      (cauchyRealCompletionInterfaceDecodeBHist (cauchyRealCompletionInterfaceEventAt 4 ef))
      (cauchyRealCompletionInterfaceDecodeBHist (cauchyRealCompletionInterfaceEventAt 5 ef))
      (cauchyRealCompletionInterfaceDecodeBHist (cauchyRealCompletionInterfaceEventAt 6 ef))
      (cauchyRealCompletionInterfaceDecodeBHist (cauchyRealCompletionInterfaceEventAt 7 ef))
      (cauchyRealCompletionInterfaceDecodeBHist (cauchyRealCompletionInterfaceEventAt 8 ef)))

private theorem CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_round_trip
    (x : CauchyRealCompletionInterfaceUp) :
    cauchyRealCompletionInterfaceFromEventFlow
        (cauchyRealCompletionInterfaceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S R B T H C P N =>
      change
        some
          (CauchyRealCompletionInterfaceUp.mk
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist D))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist S))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist R))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist B))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist T))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist H))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist C))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist P))
            (cauchyRealCompletionInterfaceDecodeBHist
              (cauchyRealCompletionInterfaceEncodeBHist N))) =
          some (CauchyRealCompletionInterfaceUp.mk D S R B T H C P N)
      rw [CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode S,
        CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode R,
        CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode B,
        CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode T,
        CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRealCompletionInterfaceUp} :
    cauchyRealCompletionInterfaceToEventFlow x =
        cauchyRealCompletionInterfaceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRealCompletionInterfaceFromEventFlow
          (cauchyRealCompletionInterfaceToEventFlow x) =
        cauchyRealCompletionInterfaceFromEventFlow
          (cauchyRealCompletionInterfaceToEventFlow y) :=
    congrArg cauchyRealCompletionInterfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyRealCompletionInterfaceUp,
      cauchyRealCompletionInterfaceFields x = cauchyRealCompletionInterfaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ S₁ R₁ B₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ S₂ R₂ B₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyRealCompletionInterfaceBHistCarrier :
    BHistCarrier CauchyRealCompletionInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRealCompletionInterfaceToEventFlow
  fromEventFlow := cauchyRealCompletionInterfaceFromEventFlow

instance cauchyRealCompletionInterfaceChapterTasteGate :
    ChapterTasteGate CauchyRealCompletionInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyRealCompletionInterfaceFromEventFlow
          (cauchyRealCompletionInterfaceToEventFlow x) =
        some x
    exact CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRealCompletionInterfaceFieldFaithful :
    FieldFaithful CauchyRealCompletionInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRealCompletionInterfaceFields
  field_faithful :=
    CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_fields_faithful

instance cauchyRealCompletionInterfaceNontrivial :
    Nontrivial CauchyRealCompletionInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRealCompletionInterfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRealCompletionInterfaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyRealCompletionInterfaceDecodeBHist
        (cauchyRealCompletionInterfaceEncodeBHist h) = h) ∧
      (∀ x : CauchyRealCompletionInterfaceUp,
        cauchyRealCompletionInterfaceFromEventFlow
          (cauchyRealCompletionInterfaceToEventFlow x) = some x) ∧
        (∀ x y : CauchyRealCompletionInterfaceUp,
          cauchyRealCompletionInterfaceToEventFlow x =
              cauchyRealCompletionInterfaceToEventFlow y →
            x = y) ∧
          cauchyRealCompletionInterfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_decode_encode,
      CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyRealCompletionInterfaceTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CauchyRealCompletionInterfaceUp
