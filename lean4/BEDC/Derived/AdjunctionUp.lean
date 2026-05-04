import BEDC.Derived.CategoryUp
import BEDC.Derived.NatTransUp
import BEDC.Derived.NatTransUp.EmptyVertComp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp
open BEDC.FKernel.Unary
open BEDC.Derived.NatTransUp

def AdjunctionUnitCounitCarrier (p q a unit counit left right : BHist) : Prop :=
  NatTransPrefixComponentCarrier p q a unit ∧
    NatTransPrefixComponentCarrier q p a counit ∧ Cont unit counit left ∧
      Cont counit unit right

def AdjunctionUnitCounitAlternating (unit counit depth : BHist) : BHist :=
  match depth with
  | BHist.Empty => BHist.Empty
  | BHist.e0 _ => BHist.Empty
  | BHist.e1 tail => append unit (AdjunctionUnitCounitAlternating counit unit tail)

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

theorem AdjunctionUnitCounitCarrier_endomorphism_unit_counit_empty
    {p a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      hsame unit BHist.Empty ∧ hsame counit BHist.Empty := by
  intro carrier
  have unitEmpty : hsame unit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.left).right.right.right
  have counitEmpty : hsame counit BHist.Empty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp
      carrier.right.left).right.right.right
  exact And.intro unitEmpty counitEmpty

theorem AdjunctionUnitCounitCarrier_endomorphism_triangles_empty
    {p a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      hsame left BHist.Empty ∧ hsame right BHist.Empty := by
  intro carrier
  have boundaryEmpty :=
    AdjunctionUnitCounitCarrier_endomorphism_unit_counit_empty carrier
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame boundaryEmpty.left boundaryEmpty.right carrier.right.right.left
      (cont_right_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame boundaryEmpty.right boundaryEmpty.left carrier.right.right.right
      (cont_right_unit BHist.Empty)
  exact And.intro leftEmpty rightEmpty

theorem AdjunctionUnitCounitCarrier_endomorphism_total_collapse
    {p a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ->
      hsame unit BHist.Empty ∧ hsame counit BHist.Empty ∧
        hsame left BHist.Empty ∧ hsame right BHist.Empty := by
  intro carrier
  have components := AdjunctionUnitCounitCarrier_endomorphism_unit_counit_empty carrier
  have triangles := AdjunctionUnitCounitCarrier_endomorphism_triangles_empty carrier
  exact
    And.intro components.left
      (And.intro components.right (And.intro triangles.left triangles.right))

theorem AdjunctionUnitCounitAlternating_endomorphism_empty
    {p a unit counit left right depth : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right -> UnaryHistory depth ->
      hsame (AdjunctionUnitCounitAlternating unit counit depth) BHist.Empty := by
  intro carrier depthUnary
  have boundaryEmpty := AdjunctionUnitCounitCarrier_endomorphism_unit_counit_empty carrier
  have alternatingEmpty :
      forall {u c depth : BHist}, hsame u BHist.Empty -> hsame c BHist.Empty ->
        UnaryHistory depth -> hsame (AdjunctionUnitCounitAlternating u c depth) BHist.Empty := by
    intro u c depth uEmpty cEmpty depthCarrier
    induction depth generalizing u c with
    | Empty =>
        exact hsame_refl BHist.Empty
    | e0 tail _ih =>
        cases depthCarrier
    | e1 tail ih =>
        have tailEmpty := ih cEmpty uEmpty depthCarrier
        cases uEmpty
        exact (append_empty_left (AdjunctionUnitCounitAlternating c BHist.Empty tail)).trans
          tailEmpty
  exact alternatingEmpty boundaryEmpty.left boundaryEmpty.right depthUnary

theorem AdjunctionUnitCounitCarrier_endomorphism_empty_components_iff
    {p a unit counit left right : BHist} :
    AdjunctionUnitCounitCarrier p p a unit counit left right ↔
      UnaryHistory p ∧ UnaryHistory a ∧ UnaryHistory unit ∧ UnaryHistory counit ∧
        hsame unit BHist.Empty ∧ hsame counit BHist.Empty ∧
          hsame left BHist.Empty ∧ hsame right BHist.Empty := by
  constructor
  · intro carrier
    have unitData :=
      Iff.mp NatTransPrefixComponentCarrier_endomorphism_component_empty_iff carrier.left
    have counitData :=
      Iff.mp NatTransPrefixComponentCarrier_endomorphism_component_empty_iff
        carrier.right.left
    have triangleData :=
      AdjunctionUnitCounitCarrier_endomorphism_triangles_empty carrier
    exact
      And.intro unitData.left
        (And.intro unitData.right.left
          (And.intro unitData.right.right.left
            (And.intro counitData.right.right.left
              (And.intro unitData.right.right.right
                (And.intro counitData.right.right.right
                  (And.intro triangleData.left triangleData.right))))))
  · intro data
    have unitCarrier : NatTransPrefixComponentCarrier p p a unit :=
      Iff.mpr NatTransPrefixComponentCarrier_endomorphism_component_empty_iff
        (And.intro data.left
          (And.intro data.right.left
            (And.intro data.right.right.left data.right.right.right.right.left)))
    have counitCarrier : NatTransPrefixComponentCarrier p p a counit :=
      Iff.mpr NatTransPrefixComponentCarrier_endomorphism_component_empty_iff
        (And.intro data.left
          (And.intro data.right.left
            (And.intro data.right.right.right.left
              data.right.right.right.right.right.left)))
    have leftRel : Cont unit counit left := by
      cases data.right.right.right.right.left
      cases data.right.right.right.right.right.left
      cases data.right.right.right.right.right.right.left
      exact cont_right_unit BHist.Empty
    have rightRel : Cont counit unit right := by
      cases data.right.right.right.right.left
      cases data.right.right.right.right.right.left
      cases data.right.right.right.right.right.right.right
      exact cont_right_unit BHist.Empty
    exact And.intro unitCarrier (And.intro counitCarrier (And.intro leftRel rightRel))

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

theorem AdjunctionPrefix_endomorphism_triangle_component_closed
    {p a eta eps left right : BHist} :
    NatTransPrefixComponentCarrier p p a eta ->
      NatTransPrefixComponentCarrier p p a eps ->
        Cont eta eps left ->
          Cont eps eta right ->
            NatTransPrefixComponentCarrier p p a left ∧
              NatTransPrefixComponentCarrier p p a right ∧ hsame left right := by
  intro etaCarrier epsCarrier leftRel rightRel
  have etaData := Iff.mp NatTransPrefixComponentCarrier_endomorphism_component_empty_iff
    etaCarrier
  have epsData := Iff.mp NatTransPrefixComponentCarrier_endomorphism_component_empty_iff
    epsCarrier
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame etaData.right.right.right epsData.right.right.right leftRel
      (cont_right_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame epsData.right.right.right etaData.right.right.right rightRel
      (cont_right_unit BHist.Empty)
  have leftCarrier : NatTransPrefixComponentCarrier p p a left :=
    Iff.mpr NatTransPrefixComponentCarrier_endomorphism_component_empty_iff
      (And.intro etaData.left
        (And.intro etaData.right.left
          (And.intro
            (unary_cont_closed etaData.right.right.left epsData.right.right.left leftRel)
            leftEmpty)))
  have rightCarrier : NatTransPrefixComponentCarrier p p a right :=
    Iff.mpr NatTransPrefixComponentCarrier_endomorphism_component_empty_iff
      (And.intro etaData.left
        (And.intro etaData.right.left
          (And.intro
            (unary_cont_closed epsData.right.right.left etaData.right.right.left rightRel)
            rightEmpty)))
  exact And.intro leftCarrier
    (And.intro rightCarrier (hsame_trans leftEmpty (hsame_symm rightEmpty)))

def AdjunctionTriangleCarrier
    (left right object unit counit leftLeg rightLeg : BHist) : Prop :=
  NatTransPrefixComponentCarrier left right object unit ∧
    NatTransPrefixComponentCarrier right left object counit ∧
      Cont unit counit leftLeg ∧ Cont counit unit rightLeg

theorem AdjunctionTriangleCarrier_empty_roundtrip_prefix_deterministic
    {left right object unit counit leftLeg rightLeg : BHist} :
    AdjunctionTriangleCarrier left right object unit counit leftLeg rightLeg ->
      hsame leftLeg BHist.Empty -> hsame rightLeg BHist.Empty -> hsame left right := by
  intro carrier leftLegEmpty rightLegEmpty
  have unitCounitEmpty : unit = BHist.Empty ∧ counit = BHist.Empty := by
    cases leftLegEmpty
    exact cont_empty_result_inversion carrier.right.right.left
  have counitUnitEmpty : counit = BHist.Empty ∧ unit = BHist.Empty := by
    cases rightLegEmpty
    exact cont_empty_result_inversion carrier.right.right.right
  cases unitCounitEmpty.left
  cases unitCounitEmpty.right
  cases counitUnitEmpty.left
  cases counitUnitEmpty.right
  have leftPrefixData :=
    (NatTransPrefixComponentCarrier_empty_identity_iff
      (p := left) (q := right) (a := object)).mp carrier.left
  have rightPrefixData :=
    (NatTransPrefixComponentCarrier_empty_identity_iff
      (p := right) (q := left) (a := object)).mp carrier.right.left
  exact hsame_trans leftPrefixData.right.right.right
    (hsame_trans rightPrefixData.right.right.right leftPrefixData.right.right.right)

theorem AdjunctionTriangleCarrier_roundtrip_empty_iff_components_empty
    {left right object unit counit leftLeg rightLeg : BHist} :
    AdjunctionTriangleCarrier left right object unit counit leftLeg rightLeg ->
      ((hsame leftLeg BHist.Empty ∧ hsame rightLeg BHist.Empty) ↔
        (hsame unit BHist.Empty ∧ hsame counit BHist.Empty)) := by
  intro carrier
  constructor
  · intro legsEmpty
    have componentEmpty : unit = BHist.Empty ∧ counit = BHist.Empty := by
      cases legsEmpty.left
      exact cont_empty_result_inversion carrier.right.right.left
    cases componentEmpty.left
    cases componentEmpty.right
    exact And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  · intro componentsEmpty
    have leftEmpty : hsame leftLeg BHist.Empty :=
      cont_respects_hsame componentsEmpty.left componentsEmpty.right carrier.right.right.left
        (cont_right_unit BHist.Empty)
    have rightEmpty : hsame rightLeg BHist.Empty :=
      cont_respects_hsame componentsEmpty.right componentsEmpty.left carrier.right.right.right
        (cont_right_unit BHist.Empty)
    exact And.intro leftEmpty rightEmpty

theorem AdjunctionPrefixEndomorphismTriangle_identity_exactness
    {p a f eta eps left right : BHist} :
    NatTransPrefixComponentCarrier p p a eta ->
      NatTransPrefixComponentCarrier p p a eps ->
        CategoryHomCarrier (append p a) (append p a) f ->
          Cont eta f left -> Cont f eps right -> hsame left f ∧ hsame right f := by
  intro etaCarrier epsCarrier _homCarrier leftContinuation rightContinuation
  have etaEmpty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp etaCarrier).right.right.right
  have epsEmpty :=
    (NatTransPrefixComponentCarrier_endomorphism_component_empty_iff.mp epsCarrier).right.right.right
  have leftEmpty : Cont BHist.Empty f left := by
    cases etaEmpty
    exact leftContinuation
  have rightEmpty : Cont f BHist.Empty right := by
    cases epsEmpty
    exact rightContinuation
  exact And.intro (cont_left_unit_result leftEmpty)
    (cont_deterministic rightEmpty (cont_right_unit f))

theorem AdjunctionPrefixComponent_cycle_empty_prefix_same {p q a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q p a theta -> Cont eta theta composite ->
        hsame composite BHist.Empty ->
          hsame p q ∧ hsame q p ∧ hsame eta BHist.Empty ∧ hsame theta BHist.Empty := by
  intro unit counit cycle compositeEmpty
  have emptyCycle : Cont eta theta BHist.Empty :=
    cont_result_hsame_transport cycle compositeEmpty
  have data :=
    Iff.mp (NatTransPrefixComponentCarrier_vert_comp_empty_iff unit counit) emptyCycle
  exact And.intro data.right.right.left
    (And.intro data.right.right.right (And.intro data.left data.right.left))

theorem AdjunctionUnitCounitCarrier_left_cycle_empty_components_iff
    {p q a unit counit left right : BHist} :
    (AdjunctionUnitCounitCarrier p q a unit counit left right ∧ hsame left BHist.Empty) ↔
      UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧ hsame p q ∧ hsame q p ∧
        hsame unit BHist.Empty ∧ hsame counit BHist.Empty ∧ hsame left BHist.Empty ∧
          hsame right BHist.Empty := by
  constructor
  · intro data
    have carrier := data.left
    have leftEmpty := data.right
    have cycleData :=
      AdjunctionPrefixComponent_cycle_empty_prefix_same carrier.left carrier.right.left
        carrier.right.right.left leftEmpty
    have unitIdentity : NatTransPrefixComponentCarrier p q a BHist.Empty := by
      cases cycleData.right.right.left
      exact carrier.left
    have unitData :=
      (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mp
        unitIdentity
    have rightEmpty : hsame right BHist.Empty :=
      cont_respects_hsame cycleData.right.right.right cycleData.right.right.left
        carrier.right.right.right (cont_right_unit BHist.Empty)
    exact
      And.intro unitData.left
        (And.intro unitData.right.left
          (And.intro unitData.right.right.left
            (And.intro cycleData.left
              (And.intro cycleData.right.left
                (And.intro cycleData.right.right.left
                  (And.intro cycleData.right.right.right
                    (And.intro leftEmpty rightEmpty)))))))
  · intro data
    have unitCarrier : NatTransPrefixComponentCarrier p q a unit := by
      cases data.right.right.right.right.right.left
      exact
        (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mpr
          (And.intro data.left
            (And.intro data.right.left
              (And.intro data.right.right.left data.right.right.right.left)))
    have counitCarrier : NatTransPrefixComponentCarrier q p a counit := by
      cases data.right.right.right.right.right.right.left
      exact
        (NatTransPrefixComponentCarrier_empty_identity_iff (p := q) (q := p) (a := a)).mpr
          (And.intro data.right.left
            (And.intro data.left
              (And.intro data.right.right.left data.right.right.right.right.left)))
    have leftRel : Cont unit counit left := by
      cases data.right.right.right.right.right.left
      cases data.right.right.right.right.right.right.left
      cases data.right.right.right.right.right.right.right.left
      exact cont_right_unit BHist.Empty
    have rightRel : Cont counit unit right := by
      cases data.right.right.right.right.right.left
      cases data.right.right.right.right.right.right.left
      cases data.right.right.right.right.right.right.right.right
      exact cont_right_unit BHist.Empty
    exact
      And.intro
        (And.intro unitCarrier (And.intro counitCarrier (And.intro leftRel rightRel)))
        data.right.right.right.right.right.right.right.left

end BEDC.Derived.AdjunctionUp
