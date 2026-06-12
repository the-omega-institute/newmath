import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNameUniformityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNameUniformityUp : Type where
  | mk (S0 S1 W R0 R1 D E H C P N : BHist) : CauchyNameUniformityUp
  deriving DecidableEq

def cauchyNameUniformityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNameUniformityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNameUniformityEncodeBHist h

def cauchyNameUniformityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNameUniformityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNameUniformityDecodeBHist tail)

theorem CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyNameUniformityFields : CauchyNameUniformityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNameUniformityUp.mk S0 S1 W R0 R1 D E H C P N =>
      [S0, S1, W, R0, R1, D, E, H, C, P, N]

def cauchyNameUniformityToEventFlow : CauchyNameUniformityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyNameUniformityFields x).map cauchyNameUniformityEncodeBHist

def cauchyNameUniformityFromEventFlow : EventFlow → Option CauchyNameUniformityUp
  -- BEDC touchpoint anchor: BHist BMark
  | S0 :: S1 :: W :: R0 :: R1 :: D :: E :: H :: C :: P :: N :: [] =>
      some
        (CauchyNameUniformityUp.mk
          (cauchyNameUniformityDecodeBHist S0)
          (cauchyNameUniformityDecodeBHist S1)
          (cauchyNameUniformityDecodeBHist W)
          (cauchyNameUniformityDecodeBHist R0)
          (cauchyNameUniformityDecodeBHist R1)
          (cauchyNameUniformityDecodeBHist D)
          (cauchyNameUniformityDecodeBHist E)
          (cauchyNameUniformityDecodeBHist H)
          (cauchyNameUniformityDecodeBHist C)
          (cauchyNameUniformityDecodeBHist P)
          (cauchyNameUniformityDecodeBHist N))
  | _ => none

private theorem cauchyNameUniformity_round_trip :
    ∀ x : CauchyNameUniformityUp,
      cauchyNameUniformityFromEventFlow (cauchyNameUniformityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 W R0 R1 D E H C P N =>
      change
        some
          (CauchyNameUniformityUp.mk
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist S0))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist S1))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist W))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist R0))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist R1))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist D))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist E))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist H))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist C))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist P))
            (cauchyNameUniformityDecodeBHist (cauchyNameUniformityEncodeBHist N))) =
          some (CauchyNameUniformityUp.mk S0 S1 W R0 R1 D E H C P N)
      rw [CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode S0,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode S1,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode W,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode R0,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode R1,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode D,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode E,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode H,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode C,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode P,
        CauchyNameUniformityTasteGate_single_carrier_alignment_decode_encode N]

private theorem cauchyNameUniformityToEventFlow_injective
    {x y : CauchyNameUniformityUp} :
    cauchyNameUniformityToEventFlow x = cauchyNameUniformityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNameUniformityFromEventFlow (cauchyNameUniformityToEventFlow x) =
        cauchyNameUniformityFromEventFlow (cauchyNameUniformityToEventFlow y) :=
    congrArg cauchyNameUniformityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyNameUniformity_round_trip x).symm
      (Eq.trans hread (cauchyNameUniformity_round_trip y)))

private theorem cauchyNameUniformity_field_faithful :
    ∀ x y : CauchyNameUniformityUp,
      cauchyNameUniformityFields x = cauchyNameUniformityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S0₁ S1₁ W₁ R0₁ R1₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S0₂ S1₂ W₂ R0₂ R1₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyNameUniformityBHistCarrier : BHistCarrier CauchyNameUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNameUniformityToEventFlow
  fromEventFlow := cauchyNameUniformityFromEventFlow

instance cauchyNameUniformityChapterTasteGate :
    ChapterTasteGate CauchyNameUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => cauchyNameUniformity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyNameUniformityToEventFlow_injective heq)

instance cauchyNameUniformityFieldFaithful : FieldFaithful CauchyNameUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyNameUniformityFields
  field_faithful := cauchyNameUniformity_field_faithful

instance cauchyNameUniformityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyNameUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyNameUniformityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyNameUniformityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyNameUniformityTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyNameUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => cauchyNameUniformity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyNameUniformityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyNameUniformityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyNameUniformityTasteGate_single_carrier_alignment

end BEDC.Derived.CauchyNameUniformityUp
