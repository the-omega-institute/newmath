import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformEquicontinuityStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformEquicontinuityStabilityUp : Type where
  | mk (K F A Q U M T R H C P N : BHist) : CompactUniformEquicontinuityStabilityUp
  deriving DecidableEq

def compactUniformEquicontinuityStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformEquicontinuityStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformEquicontinuityStabilityEncodeBHist h

def compactUniformEquicontinuityStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformEquicontinuityStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformEquicontinuityStabilityDecodeBHist tail)

private theorem CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactUniformEquicontinuityStabilityDecodeBHist
        (compactUniformEquicontinuityStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformEquicontinuityStabilityFields :
    CompactUniformEquicontinuityStabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformEquicontinuityStabilityUp.mk K F A Q U M T R H C P N =>
      [K, F, A, Q, U, M, T, R, H, C, P, N]

def compactUniformEquicontinuityStabilityToEventFlow :
    CompactUniformEquicontinuityStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactUniformEquicontinuityStabilityFields x).map
        compactUniformEquicontinuityStabilityEncodeBHist

def compactUniformEquicontinuityStabilityFromEventFlow :
    EventFlow → Option CompactUniformEquicontinuityStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [K, F, A, Q, U, M, T, R, H, C, P, N] =>
      some
        (CompactUniformEquicontinuityStabilityUp.mk
          (compactUniformEquicontinuityStabilityDecodeBHist K)
          (compactUniformEquicontinuityStabilityDecodeBHist F)
          (compactUniformEquicontinuityStabilityDecodeBHist A)
          (compactUniformEquicontinuityStabilityDecodeBHist Q)
          (compactUniformEquicontinuityStabilityDecodeBHist U)
          (compactUniformEquicontinuityStabilityDecodeBHist M)
          (compactUniformEquicontinuityStabilityDecodeBHist T)
          (compactUniformEquicontinuityStabilityDecodeBHist R)
          (compactUniformEquicontinuityStabilityDecodeBHist H)
          (compactUniformEquicontinuityStabilityDecodeBHist C)
          (compactUniformEquicontinuityStabilityDecodeBHist P)
          (compactUniformEquicontinuityStabilityDecodeBHist N))
  | _ => none

private theorem CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformEquicontinuityStabilityUp,
      compactUniformEquicontinuityStabilityFromEventFlow
        (compactUniformEquicontinuityStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F A Q U M T R H C P N =>
      change
        some
          (CompactUniformEquicontinuityStabilityUp.mk
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist K))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist F))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist A))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist Q))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist U))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist M))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist T))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist R))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist H))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist C))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist P))
            (compactUniformEquicontinuityStabilityDecodeBHist
              (compactUniformEquicontinuityStabilityEncodeBHist N))) =
          some (CompactUniformEquicontinuityStabilityUp.mk K F A Q U M T R H C P N)
      rw [CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode K,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode F,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode A,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode Q,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode U,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode M,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode T,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode R,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode H,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode C,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode P,
        CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode N]

private theorem CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_injective
    {x y : CompactUniformEquicontinuityStabilityUp} :
    compactUniformEquicontinuityStabilityToEventFlow x =
      compactUniformEquicontinuityStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformEquicontinuityStabilityFromEventFlow
          (compactUniformEquicontinuityStabilityToEventFlow x) =
        compactUniformEquicontinuityStabilityFromEventFlow
          (compactUniformEquicontinuityStabilityToEventFlow y) :=
    congrArg compactUniformEquicontinuityStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompactUniformEquicontinuityStabilityUp,
      compactUniformEquicontinuityStabilityFields x =
        compactUniformEquicontinuityStabilityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ A₁ Q₁ U₁ M₁ T₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ A₂ Q₂ U₂ M₂ T₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactUniformEquicontinuityStabilityBHistCarrier :
    BHistCarrier CompactUniformEquicontinuityStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformEquicontinuityStabilityToEventFlow
  fromEventFlow := compactUniformEquicontinuityStabilityFromEventFlow

instance compactUniformEquicontinuityStabilityChapterTasteGate :
    ChapterTasteGate CompactUniformEquicontinuityStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformEquicontinuityStabilityFromEventFlow
        (compactUniformEquicontinuityStabilityToEventFlow x) = some x
    exact CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_injective heq)

instance compactUniformEquicontinuityStabilityFieldFaithful :
    FieldFaithful CompactUniformEquicontinuityStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactUniformEquicontinuityStabilityFields
  field_faithful :=
    CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate CompactUniformEquicontinuityStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformEquicontinuityStabilityChapterTasteGate

theorem CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformEquicontinuityStabilityDecodeBHist
        (compactUniformEquicontinuityStabilityEncodeBHist h) = h) ∧
      (∀ K F A Q U M T R H C P N : BHist,
        compactUniformEquicontinuityStabilityFields
            (CompactUniformEquicontinuityStabilityUp.mk K F A Q U M T R H C P N) =
          [K, F, A, Q, U, M, T, R, H, C, P, N]) ∧
        compactUniformEquicontinuityStabilityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CompactUniformEquicontinuityStabilityTasteGate_single_carrier_alignment_decode
  · constructor
    · intro K F A Q U M T R H C P N
      rfl
    · rfl

end BEDC.Derived.CompactUniformEquicontinuityStabilityUp
