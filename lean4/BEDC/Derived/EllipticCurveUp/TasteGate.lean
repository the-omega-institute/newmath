import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EllipticCurveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EllipticCurveUp : Type where
  | mk
      (field projective a1 a2 a3 a4 a6 cubic smooth basepoint fieldClassifier
        projectiveClassifier provenance : BHist) :
      EllipticCurveUp
  deriving DecidableEq

def ellipticCurveEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ellipticCurveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ellipticCurveEncodeBHist h

def ellipticCurveDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ellipticCurveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ellipticCurveDecodeBHist tail)

private theorem EllipticCurveTasteGate_single_carrier_alignment_decode :
    forall h : BHist, ellipticCurveDecodeBHist (ellipticCurveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ellipticCurveFields : EllipticCurveUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EllipticCurveUp.mk field projective a1 a2 a3 a4 a6 cubic smooth basepoint
      fieldClassifier projectiveClassifier provenance =>
      [field, projective, a1, a2, a3, a4, a6, cubic, smooth, basepoint, fieldClassifier,
        projectiveClassifier, provenance]

def ellipticCurveToEventFlow : EllipticCurveUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ellipticCurveFields x).map ellipticCurveEncodeBHist

def ellipticCurveFromEventFlow : EventFlow -> Option EllipticCurveUp
  -- BEDC touchpoint anchor: BHist BMark
  | field :: projective :: a1 :: a2 :: a3 :: a4 :: a6 :: cubic :: smooth :: basepoint ::
      fieldClassifier :: projectiveClassifier :: provenance :: [] =>
      some
        (EllipticCurveUp.mk
          (ellipticCurveDecodeBHist field)
          (ellipticCurveDecodeBHist projective)
          (ellipticCurveDecodeBHist a1)
          (ellipticCurveDecodeBHist a2)
          (ellipticCurveDecodeBHist a3)
          (ellipticCurveDecodeBHist a4)
          (ellipticCurveDecodeBHist a6)
          (ellipticCurveDecodeBHist cubic)
          (ellipticCurveDecodeBHist smooth)
          (ellipticCurveDecodeBHist basepoint)
          (ellipticCurveDecodeBHist fieldClassifier)
          (ellipticCurveDecodeBHist projectiveClassifier)
          (ellipticCurveDecodeBHist provenance))
  | _ => none

private theorem EllipticCurveTasteGate_single_carrier_alignment_round_trip :
    forall x : EllipticCurveUp,
      ellipticCurveFromEventFlow (ellipticCurveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk field projective a1 a2 a3 a4 a6 cubic smooth basepoint fieldClassifier
      projectiveClassifier provenance =>
      change
        some
          (EllipticCurveUp.mk
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist field))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist projective))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist a1))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist a2))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist a3))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist a4))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist a6))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist cubic))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist smooth))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist basepoint))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist fieldClassifier))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist projectiveClassifier))
            (ellipticCurveDecodeBHist (ellipticCurveEncodeBHist provenance))) =
          some
            (EllipticCurveUp.mk field projective a1 a2 a3 a4 a6 cubic smooth basepoint
              fieldClassifier projectiveClassifier provenance)
      rw [EllipticCurveTasteGate_single_carrier_alignment_decode field,
        EllipticCurveTasteGate_single_carrier_alignment_decode projective,
        EllipticCurveTasteGate_single_carrier_alignment_decode a1,
        EllipticCurveTasteGate_single_carrier_alignment_decode a2,
        EllipticCurveTasteGate_single_carrier_alignment_decode a3,
        EllipticCurveTasteGate_single_carrier_alignment_decode a4,
        EllipticCurveTasteGate_single_carrier_alignment_decode a6,
        EllipticCurveTasteGate_single_carrier_alignment_decode cubic,
        EllipticCurveTasteGate_single_carrier_alignment_decode smooth,
        EllipticCurveTasteGate_single_carrier_alignment_decode basepoint,
        EllipticCurveTasteGate_single_carrier_alignment_decode fieldClassifier,
        EllipticCurveTasteGate_single_carrier_alignment_decode projectiveClassifier,
        EllipticCurveTasteGate_single_carrier_alignment_decode provenance]

private theorem EllipticCurveTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EllipticCurveUp} :
    ellipticCurveToEventFlow x = ellipticCurveToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ellipticCurveFromEventFlow (ellipticCurveToEventFlow x) =
        ellipticCurveFromEventFlow (ellipticCurveToEventFlow y) :=
    congrArg ellipticCurveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EllipticCurveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EllipticCurveTasteGate_single_carrier_alignment_round_trip y)))

private theorem EllipticCurveTasteGate_single_carrier_alignment_fields :
    forall x y : EllipticCurveUp, ellipticCurveFields x = ellipticCurveFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk field1 projective1 a11 a21 a31 a41 a61 cubic1 smooth1 basepoint1
      fieldClassifier1 projectiveClassifier1 provenance1 =>
      cases y with
      | mk field2 projective2 a12 a22 a32 a42 a62 cubic2 smooth2 basepoint2
          fieldClassifier2 projectiveClassifier2 provenance2 =>
          cases hfields
          rfl

instance ellipticCurveBHistCarrier : BHistCarrier EllipticCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ellipticCurveToEventFlow
  fromEventFlow := ellipticCurveFromEventFlow

instance ellipticCurveChapterTasteGate : ChapterTasteGate EllipticCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ellipticCurveFromEventFlow (ellipticCurveToEventFlow x) = some x
    exact EllipticCurveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EllipticCurveTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ellipticCurveFieldFaithful : FieldFaithful EllipticCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ellipticCurveFields
  field_faithful := EllipticCurveTasteGate_single_carrier_alignment_fields

instance ellipticCurveNontrivial : BEDC.Meta.TasteGate.Nontrivial EllipticCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EllipticCurveUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      EllipticCurveUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EllipticCurveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ellipticCurveChapterTasteGate

namespace TasteGate

theorem EllipticCurveTasteGate_single_carrier_alignment :
    (∀ h : BHist, ellipticCurveDecodeBHist (ellipticCurveEncodeBHist h) = h) ∧
      (∀ x : EllipticCurveUp,
        ellipticCurveToEventFlow x = List.map ellipticCurveEncodeBHist (ellipticCurveFields x)) ∧
      (∀ x y : EllipticCurveUp, ellipticCurveFields x = ellipticCurveFields y -> x = y) ∧
      (∃ x y : EllipticCurveUp, x ≠ y) ∧
      ellipticCurveEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    And.intro EllipticCurveTasteGate_single_carrier_alignment_decode
      (And.intro
        (by
          intro x
          rfl)
        (And.intro EllipticCurveTasteGate_single_carrier_alignment_fields
          (And.intro
            (by
              exact
                ⟨EllipticCurveUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty,
                  EllipticCurveUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                  by
                    intro h
                    cases h⟩)
            rfl)))

end TasteGate

end BEDC.Derived.EllipticCurveUp
