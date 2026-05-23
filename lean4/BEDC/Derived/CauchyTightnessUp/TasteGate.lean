import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTightnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTightnessUp : Type where
  | mk (B G M D R L E H C P N : BHist) : CauchyTightnessUp
  deriving DecidableEq

def cauchyTightnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTightnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTightnessEncodeBHist h

def cauchyTightnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTightnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTightnessDecodeBHist tail)

private theorem CauchyTightnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTightnessFields : CauchyTightnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTightnessUp.mk B G M D R L E H C P N => [B, G, M, D, R, L, E, H, C, P, N]

def cauchyTightnessToEventFlow : CauchyTightnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTightnessFields x).map cauchyTightnessEncodeBHist

private def cauchyTightnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyTightnessEventAt index rest

def cauchyTightnessFromEventFlow (ef : EventFlow) : Option CauchyTightnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyTightnessUp.mk
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 0 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 1 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 2 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 3 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 4 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 5 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 6 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 7 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 8 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 9 ef))
      (cauchyTightnessDecodeBHist (cauchyTightnessEventAt 10 ef)))

private theorem CauchyTightnessTasteGate_single_carrier_alignment_round_trip
    (x : CauchyTightnessUp) :
    cauchyTightnessFromEventFlow (cauchyTightnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B G M D R L E H C P N =>
      change
        some
          (CauchyTightnessUp.mk
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist B))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist G))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist M))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist D))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist R))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist L))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist E))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist H))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist C))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist P))
            (cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist N))) =
          some (CauchyTightnessUp.mk B G M D R L E H C P N)
      rw [CauchyTightnessTasteGate_single_carrier_alignment_decode_encode B,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode G,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode M,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode D,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode R,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode L,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode E,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode H,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode C,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode P,
        CauchyTightnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyTightnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTightnessUp} :
    cauchyTightnessToEventFlow x = cauchyTightnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTightnessFromEventFlow (cauchyTightnessToEventFlow x) =
        cauchyTightnessFromEventFlow (cauchyTightnessToEventFlow y) :=
    congrArg cauchyTightnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTightnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyTightnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyTightnessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyTightnessUp, cauchyTightnessFields x = cauchyTightnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ G₁ M₁ D₁ R₁ L₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ G₂ M₂ D₂ R₂ L₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyTightnessBHistCarrier : BHistCarrier CauchyTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTightnessToEventFlow
  fromEventFlow := cauchyTightnessFromEventFlow

instance cauchyTightnessChapterTasteGate : ChapterTasteGate CauchyTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTightnessFromEventFlow (cauchyTightnessToEventFlow x) = some x
    exact CauchyTightnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyTightnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyTightnessFieldFaithful : FieldFaithful CauchyTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTightnessFields
  field_faithful := CauchyTightnessTasteGate_single_carrier_alignment_fields_faithful

instance cauchyTightnessNontrivial : Nontrivial CauchyTightnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyTightnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyTightnessUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyTightnessTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyTightnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTightnessChapterTasteGate

theorem CauchyTightnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTightnessDecodeBHist (cauchyTightnessEncodeBHist h) = h) ∧
      (∀ x : CauchyTightnessUp,
        cauchyTightnessFromEventFlow (cauchyTightnessToEventFlow x) = some x) ∧
        (∀ x y : CauchyTightnessUp,
          cauchyTightnessToEventFlow x = cauchyTightnessToEventFlow y → x = y) ∧
          cauchyTightnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyTightnessTasteGate_single_carrier_alignment_decode_encode,
      CauchyTightnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyTightnessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyTightnessUp
