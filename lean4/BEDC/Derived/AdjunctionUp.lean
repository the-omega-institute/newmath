import BEDC.Derived.NatTransUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatTransUp

def AdjunctionUnitCounitCarrier (p q a unit counit left right : BHist) : Prop :=
  NatTransPrefixComponentCarrier p q a unit ∧
    NatTransPrefixComponentCarrier q p a counit ∧ Cont unit counit left ∧
      Cont counit unit right

theorem AdjunctionUnitCounitCarrier_empty_components_exact {p q a composite : BHist} :
    AdjunctionUnitCounitCarrier p q a BHist.Empty BHist.Empty composite composite ↔
      UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧ hsame p q ∧
        hsame composite BHist.Empty := by
  constructor
  · intro carrier
    have unitData :=
      (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mp
        carrier.left
    exact
      And.intro unitData.left
        (And.intro unitData.right.left
          (And.intro unitData.right.right.left
            (And.intro unitData.right.right.right
              (cont_left_unit_result carrier.right.right.left))))
  · intro data
    cases data with
    | intro pCarrier rest =>
        cases rest with
        | intro qCarrier rest =>
            cases rest with
            | intro aCarrier rest =>
                cases rest with
                | intro samePQ compositeEmpty =>
                    exact
                      And.intro
                        ((NatTransPrefixComponentCarrier_empty_identity_iff
                          (p := p) (q := q) (a := a)).mpr
                          (And.intro pCarrier
                            (And.intro qCarrier (And.intro aCarrier samePQ))))
                        (And.intro
                          ((NatTransPrefixComponentCarrier_empty_identity_iff
                            (p := q) (q := p) (a := a)).mpr
                            (And.intro qCarrier
                              (And.intro pCarrier
                                (And.intro aCarrier (hsame_symm samePQ)))))
                          (And.intro
                            (cont_left_unit_iff.mpr compositeEmpty)
                            (cont_left_unit_iff.mpr compositeEmpty)))

theorem Adjunction_empty_unit_counit_prefix_iff {p q a : BHist} :
    (NatTransPrefixComponentCarrier p q a BHist.Empty ∧
      NatTransPrefixComponentCarrier q p a BHist.Empty ∧
        Cont BHist.Empty BHist.Empty BHist.Empty) ↔
      UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧ hsame p q := by
  constructor
  · intro data
    cases data with
    | intro unitData rest =>
        exact (NatTransPrefixComponentCarrier_empty_identity_iff
          (p := p) (q := q) (a := a)).mp unitData
  · intro data
    cases data with
    | intro pCarrier rest =>
        cases rest with
        | intro qCarrier rest =>
            cases rest with
            | intro aCarrier samePrefix =>
                exact
                  And.intro
                    ((NatTransPrefixComponentCarrier_empty_identity_iff
                      (p := p) (q := q) (a := a)).mpr
                      (And.intro pCarrier
                        (And.intro qCarrier (And.intro aCarrier samePrefix))))
                    (And.intro
                      ((NatTransPrefixComponentCarrier_empty_identity_iff
                        (p := q) (q := p) (a := a)).mpr
                        (And.intro qCarrier
                          (And.intro pCarrier
                            (And.intro aCarrier (hsame_symm samePrefix)))))
                      (cont_intro rfl))

theorem AdjunctionUnitCounitCarrier_empty_components_iff {p q a left right : BHist} :
    AdjunctionUnitCounitCarrier p q a BHist.Empty BHist.Empty left right ↔
      UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧ hsame p q ∧
        hsame left BHist.Empty ∧ hsame right BHist.Empty := by
  constructor
  · intro carrier
    have unitData :=
      (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mp
        carrier.left
    have leftEmpty : hsame left BHist.Empty :=
      cont_deterministic carrier.right.right.left (cont_right_unit BHist.Empty)
    have rightEmpty : hsame right BHist.Empty :=
      cont_deterministic carrier.right.right.right (cont_right_unit BHist.Empty)
    exact
      And.intro unitData.left
        (And.intro unitData.right.left
          (And.intro unitData.right.right.left
            (And.intro unitData.right.right.right (And.intro leftEmpty rightEmpty))))
  · intro data
    have unitCarrier : NatTransPrefixComponentCarrier p q a BHist.Empty :=
      (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mpr
        (And.intro data.left
          (And.intro data.right.left
            (And.intro data.right.right.left data.right.right.right.left)))
    have counitCarrier : NatTransPrefixComponentCarrier q p a BHist.Empty :=
      (NatTransPrefixComponentCarrier_empty_identity_iff (p := q) (q := p) (a := a)).mpr
        (And.intro data.right.left
          (And.intro data.left
            (And.intro data.right.right.left (hsame_symm data.right.right.right.left))))
    have leftRel : Cont BHist.Empty BHist.Empty left := by
      cases data.right.right.right.right.left
      exact cont_right_unit BHist.Empty
    have rightRel : Cont BHist.Empty BHist.Empty right := by
      cases data.right.right.right.right.right
      exact cont_right_unit BHist.Empty
    exact And.intro unitCarrier (And.intro counitCarrier (And.intro leftRel rightRel))

theorem AdjunctionUnitCounitCarrier_triangle_results_deterministic
    {p q a unit counit left right left' right' : BHist} :
    AdjunctionUnitCounitCarrier p q a unit counit left right ->
      Cont unit counit left' -> Cont counit unit right' ->
        hsame left left' ∧ hsame right right' := by
  intro carrier leftRel rightRel
  exact
    And.intro
      (cont_deterministic carrier.right.right.left leftRel)
      (cont_deterministic carrier.right.right.right rightRel)

theorem AdjunctionPrefix_unit_counit_composite_empty
    {p q a eta eps composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q p a eps -> Cont eta eps composite ->
        NatTransPrefixComponentCarrier p p a composite ∧ hsame composite BHist.Empty := by
  intro unitComponent counitComponent compositeRel
  have compositeComponent :
      NatTransPrefixComponentCarrier p p a composite :=
    NatTransPrefixComponentCarrier_vert_comp_closed unitComponent counitComponent compositeRel
  have endomorphismData :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff
      (p := p) (a := a) (eta := composite)).mp compositeComponent
  exact And.intro compositeComponent endomorphismData.right.right.right

end BEDC.Derived.AdjunctionUp
