import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricContinuousImageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactMetricContinuousImageUp : Type where
  | mk (K F M U E T H C P N : BHist) : CompactMetricContinuousImageUp
  deriving DecidableEq

def compactMetricContinuousImageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactMetricContinuousImageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactMetricContinuousImageEncodeBHist h

def compactMetricContinuousImageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactMetricContinuousImageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactMetricContinuousImageDecodeBHist tail)

theorem CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactMetricContinuousImageDecodeBHist
        (compactMetricContinuousImageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactMetricContinuousImageFields :
    CompactMetricContinuousImageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricContinuousImageUp.mk K F M U E T H C P N =>
      [K, F, M, U, E, T, H, C, P, N]

def compactMetricContinuousImageToEventFlow :
    CompactMetricContinuousImageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactMetricContinuousImageFields x).map
        compactMetricContinuousImageEncodeBHist

def compactMetricContinuousImageFromEventFlow :
    EventFlow → Option CompactMetricContinuousImageUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _K :: [] => none
  | _K :: _F :: [] => none
  | _K :: _F :: _M :: [] => none
  | _K :: _F :: _M :: _U :: [] => none
  | _K :: _F :: _M :: _U :: _E :: [] => none
  | _K :: _F :: _M :: _U :: _E :: _T :: [] => none
  | _K :: _F :: _M :: _U :: _E :: _T :: _H :: [] => none
  | _K :: _F :: _M :: _U :: _E :: _T :: _H :: _C :: [] => none
  | _K :: _F :: _M :: _U :: _E :: _T :: _H :: _C :: _P :: [] => none
  | K :: F :: M :: U :: E :: T :: H :: C :: P :: N :: [] =>
      some
        (CompactMetricContinuousImageUp.mk
          (compactMetricContinuousImageDecodeBHist K)
          (compactMetricContinuousImageDecodeBHist F)
          (compactMetricContinuousImageDecodeBHist M)
          (compactMetricContinuousImageDecodeBHist U)
          (compactMetricContinuousImageDecodeBHist E)
          (compactMetricContinuousImageDecodeBHist T)
          (compactMetricContinuousImageDecodeBHist H)
          (compactMetricContinuousImageDecodeBHist C)
          (compactMetricContinuousImageDecodeBHist P)
          (compactMetricContinuousImageDecodeBHist N))
  | _K :: _F :: _M :: _U :: _E :: _T :: _H :: _C :: _P :: _N :: _extra :: _rest =>
      none

theorem CompactMetricContinuousImageTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactMetricContinuousImageUp,
      compactMetricContinuousImageFromEventFlow
        (compactMetricContinuousImageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M U E T H C P N =>
      change
        some
          (CompactMetricContinuousImageUp.mk
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist K))
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist F))
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist M))
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist U))
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist E))
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist T))
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist H))
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist C))
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist P))
            (compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist N))) =
          some (CompactMetricContinuousImageUp.mk K F M U E T H C P N)
      rw [CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode K,
        CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode F,
        CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode M,
        CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode U,
        CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode E,
        CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode T,
        CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode H,
        CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode C,
        CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode P,
        CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode N]

theorem CompactMetricContinuousImageTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactMetricContinuousImageUp} :
    compactMetricContinuousImageToEventFlow x =
      compactMetricContinuousImageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactMetricContinuousImageFromEventFlow
          (compactMetricContinuousImageToEventFlow x) =
        compactMetricContinuousImageFromEventFlow
          (compactMetricContinuousImageToEventFlow y) :=
    congrArg compactMetricContinuousImageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactMetricContinuousImageTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactMetricContinuousImageTasteGate_single_carrier_alignment_round_trip y)))

theorem CompactMetricContinuousImageTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CompactMetricContinuousImageUp,
      compactMetricContinuousImageFields x = compactMetricContinuousImageFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk K₁ F₁ M₁ U₁ E₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ M₂ U₂ E₂ T₂ H₂ C₂ P₂ N₂ =>
          injection h with hK restF
          injection restF with hF restM
          injection restM with hM restU
          injection restU with hU restE
          injection restE with hE restT
          injection restT with hT restH
          injection restH with hH restC
          injection restC with hC restP
          injection restP with hP restN
          injection restN with hN _
          subst hK
          subst hF
          subst hM
          subst hU
          subst hE
          subst hT
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance compactMetricContinuousImageBHistCarrier :
    BHistCarrier CompactMetricContinuousImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactMetricContinuousImageToEventFlow
  fromEventFlow := compactMetricContinuousImageFromEventFlow

instance compactMetricContinuousImageChapterTasteGate :
    ChapterTasteGate CompactMetricContinuousImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactMetricContinuousImageFromEventFlow
        (compactMetricContinuousImageToEventFlow x) = some x
    exact CompactMetricContinuousImageTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactMetricContinuousImageTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compactMetricContinuousImageFieldFaithful :
    FieldFaithful CompactMetricContinuousImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactMetricContinuousImageFields
  field_faithful := CompactMetricContinuousImageTasteGate_single_carrier_alignment_field_faithful

instance compactMetricContinuousImageNontrivial :
    Nontrivial CompactMetricContinuousImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactMetricContinuousImageUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactMetricContinuousImageUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def compactMetricContinuousImageTasteGate :
    ChapterTasteGate CompactMetricContinuousImageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactMetricContinuousImageChapterTasteGate

theorem CompactMetricContinuousImageTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactMetricContinuousImageUp) ∧
      Nonempty (FieldFaithful CompactMetricContinuousImageUp) ∧
        Nonempty (Nontrivial CompactMetricContinuousImageUp) ∧
          (∀ h : BHist,
            compactMetricContinuousImageDecodeBHist
              (compactMetricContinuousImageEncodeBHist h) = h) ∧
            (∀ x : CompactMetricContinuousImageUp,
              compactMetricContinuousImageFromEventFlow
                (compactMetricContinuousImageToEventFlow x) = some x) ∧
              compactMetricContinuousImageEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨compactMetricContinuousImageChapterTasteGate⟩
  · constructor
    · exact ⟨compactMetricContinuousImageFieldFaithful⟩
    · constructor
      · exact ⟨compactMetricContinuousImageNontrivial⟩
      · constructor
        · exact CompactMetricContinuousImageTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact CompactMetricContinuousImageTasteGate_single_carrier_alignment_round_trip
          · rfl

end BEDC.Derived.CompactMetricContinuousImageUp
