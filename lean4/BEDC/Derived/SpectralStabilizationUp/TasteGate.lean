import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpectralStabilizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpectralStabilizationUp : Type where
  | mk (W M I K R L U H C P N : BHist) : SpectralStabilizationUp
  deriving DecidableEq

def spectralStabilizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: spectralStabilizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: spectralStabilizationEncodeBHist h

def spectralStabilizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (spectralStabilizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (spectralStabilizationDecodeBHist tail)

private theorem spectralStabilization_decode_encode :
    ∀ h : BHist, spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def spectralStabilizationFields : SpectralStabilizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpectralStabilizationUp.mk W M I K R L U H C P N => [W, M, I, K, R, L, U, H, C, P, N]

def spectralStabilizationToEventFlow : SpectralStabilizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (spectralStabilizationFields x).map spectralStabilizationEncodeBHist

def spectralStabilizationFromEventFlow : EventFlow → Option SpectralStabilizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | W :: M :: I :: K :: R :: L :: U :: H :: C :: P :: N :: [] =>
      some
        (SpectralStabilizationUp.mk
          (spectralStabilizationDecodeBHist W)
          (spectralStabilizationDecodeBHist M)
          (spectralStabilizationDecodeBHist I)
          (spectralStabilizationDecodeBHist K)
          (spectralStabilizationDecodeBHist R)
          (spectralStabilizationDecodeBHist L)
          (spectralStabilizationDecodeBHist U)
          (spectralStabilizationDecodeBHist H)
          (spectralStabilizationDecodeBHist C)
          (spectralStabilizationDecodeBHist P)
          (spectralStabilizationDecodeBHist N))
  | _ => none

private theorem spectralStabilization_round_trip :
    ∀ x : SpectralStabilizationUp,
      spectralStabilizationFromEventFlow (spectralStabilizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W M I K R L U H C P N =>
      change
        some
          (SpectralStabilizationUp.mk
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist W))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist M))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist I))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist K))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist R))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist L))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist U))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist H))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist C))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist P))
            (spectralStabilizationDecodeBHist (spectralStabilizationEncodeBHist N))) =
          some (SpectralStabilizationUp.mk W M I K R L U H C P N)
      rw [spectralStabilization_decode_encode W, spectralStabilization_decode_encode M,
        spectralStabilization_decode_encode I, spectralStabilization_decode_encode K,
        spectralStabilization_decode_encode R, spectralStabilization_decode_encode L,
        spectralStabilization_decode_encode U, spectralStabilization_decode_encode H,
        spectralStabilization_decode_encode C, spectralStabilization_decode_encode P,
        spectralStabilization_decode_encode N]

private theorem spectralStabilizationToEventFlow_injective {x y : SpectralStabilizationUp} :
    spectralStabilizationToEventFlow x = spectralStabilizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      spectralStabilizationFromEventFlow (spectralStabilizationToEventFlow x) =
        spectralStabilizationFromEventFlow (spectralStabilizationToEventFlow y) :=
    congrArg spectralStabilizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (spectralStabilization_round_trip x).symm
      (Eq.trans hread (spectralStabilization_round_trip y)))

private theorem spectralStabilization_fields_faithful :
    ∀ x y : SpectralStabilizationUp, spectralStabilizationFields x = spectralStabilizationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W₁ M₁ I₁ K₁ R₁ L₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk W₂ M₂ I₂ K₂ R₂ L₂ U₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hW tail0
          injection tail0 with hM tail1
          injection tail1 with hI tail2
          injection tail2 with hK tail3
          injection tail3 with hR tail4
          injection tail4 with hL tail5
          injection tail5 with hU tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hW
          subst hM
          subst hI
          subst hK
          subst hR
          subst hL
          subst hU
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance spectralStabilizationBHistCarrier : BHistCarrier SpectralStabilizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := spectralStabilizationToEventFlow
  fromEventFlow := spectralStabilizationFromEventFlow

instance spectralStabilizationChapterTasteGate : ChapterTasteGate SpectralStabilizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change spectralStabilizationFromEventFlow (spectralStabilizationToEventFlow x) = some x
    exact spectralStabilization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (spectralStabilizationToEventFlow_injective heq)

instance spectralStabilizationFieldFaithful : FieldFaithful SpectralStabilizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := spectralStabilizationFields
  field_faithful := spectralStabilization_fields_faithful

instance spectralStabilizationNontrivial : Nontrivial SpectralStabilizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SpectralStabilizationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SpectralStabilizationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SpectralStabilizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  spectralStabilizationChapterTasteGate

end BEDC.Derived.SpectralStabilizationUp
