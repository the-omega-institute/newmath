import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.FilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FilterPrincipalSuffix_unary_intersection_closed
    {base left right meet leftPoint rightPoint meetPoint : BHist} :
    UnaryHistory base -> UnaryHistory left -> UnaryHistory right -> Cont left right meet ->
      Cont base left leftPoint -> Cont base right rightPoint -> Cont base meet meetPoint ->
        UnaryHistory meetPoint ∧ Cont leftPoint right meetPoint ∧
          Cont rightPoint left meetPoint := by
  intro baseCarrier leftCarrier rightCarrier leftRight baseLeft baseRight baseMeet
  have meetCarrier : UnaryHistory meet :=
    unary_cont_closed leftCarrier rightCarrier leftRight
  have meetPointCarrier : UnaryHistory meetPoint :=
    unary_cont_closed baseCarrier meetCarrier baseMeet
  have leftProjection : Cont leftPoint right meetPoint := by
    cases baseMeet
    cases baseLeft
    cases leftRight
    exact cont_intro (append_assoc base left right).symm
  have rightProjection : Cont rightPoint left meetPoint := by
    cases baseMeet
    cases baseRight
    cases leftRight
    exact cont_intro
      ((congrArg (fun tail => append base tail)
        (unary_append_comm leftCarrier rightCarrier)).trans
          (append_assoc base right left).symm)
  exact And.intro meetPointCarrier (And.intro leftProjection rightProjection)

theorem FilterPrincipalSuffix_unary_intersection_result_deterministic
    {base left right meet leftPoint rightPoint meetPoint displayed : BHist} :
    UnaryHistory base -> UnaryHistory left -> UnaryHistory right -> Cont left right meet ->
      Cont base left leftPoint -> Cont base right rightPoint -> Cont base meet meetPoint ->
        Cont rightPoint left displayed -> hsame meetPoint displayed := by
  intro baseCarrier leftCarrier rightCarrier leftRight baseLeft baseRight baseMeet displayedRel
  have closed :=
    FilterPrincipalSuffix_unary_intersection_closed
      baseCarrier leftCarrier rightCarrier leftRight baseLeft baseRight baseMeet
  exact cont_deterministic closed.right.right displayedRel

theorem FilterPrincipalSuffix_unary_commuting_square
    {base left right leftPoint rightPoint lrPoint rlPoint : BHist} :
    UnaryHistory left -> UnaryHistory right -> Cont base left leftPoint ->
      Cont base right rightPoint -> Cont leftPoint right lrPoint ->
        Cont rightPoint left rlPoint -> hsame lrPoint rlPoint := by
  intro leftCarrier rightCarrier baseLeft baseRight leftThenRight rightThenLeft
  cases baseLeft
  cases baseRight
  cases leftThenRight
  cases rightThenLeft
  exact hsame_trans (append_assoc base left right)
    (hsame_trans
      (congrArg (fun tail => append base tail)
        (unary_append_comm leftCarrier rightCarrier))
      (hsame_symm (append_assoc base right left)))

theorem FilterPrincipalSuffix_unary_commuting_square_base_deterministic
    {base base' left right leftPoint rightPoint meetPoint : BHist} :
    UnaryHistory left -> UnaryHistory right -> Cont base left leftPoint ->
      Cont base' right rightPoint -> Cont leftPoint right meetPoint ->
        Cont rightPoint left meetPoint -> hsame base base' := by
  intro leftCarrier rightCarrier baseLeft baseRight leftThenRight rightThenLeft
  cases baseLeft
  cases baseRight
  have samePaths : hsame (append (append base left) right) (append (append base' right) left) :=
    leftThenRight.symm.trans rightThenLeft
  have sameCommonSuffix : hsame (append base (append left right)) (append base' (append left right)) :=
    (append_assoc base left right).symm.trans
      (samePaths.trans
        ((append_assoc base' right left).trans
          (congrArg (append base') (unary_append_comm leftCarrier rightCarrier).symm)))
  exact append_right_cancel (k := append left right) sameCommonSuffix

theorem FilterPrincipalSuffix_unary_intersection_meet_commutes {left right meet commute : BHist} :
    UnaryHistory left -> UnaryHistory right -> Cont left right meet -> Cont right left commute ->
      hsame meet commute := by
  intro leftCarrier rightCarrier leftRight rightLeft
  exact FilterPrincipalSuffix_unary_commuting_square leftCarrier rightCarrier
    (cont_left_unit left) (cont_left_unit right) leftRight rightLeft

theorem FilterPrincipalSuffix_unary_intersection_commuted_meet_closed
    {base left right meet meetPoint : BHist} :
    UnaryHistory left -> UnaryHistory right -> Cont left right meet -> Cont base meet meetPoint ->
      Cont base (append right left) meetPoint := by
  intro leftCarrier rightCarrier leftRight baseMeet
  cases baseMeet
  cases leftRight
  exact cont_intro (congrArg (fun tail => append base tail)
    (unary_append_comm leftCarrier rightCarrier))

theorem FilterPrincipalSuffix_unary_intersection_commuted_result_deterministic
    {base left right meet meetPoint displayed : BHist} :
    UnaryHistory left -> UnaryHistory right -> Cont left right meet -> Cont base meet meetPoint ->
      Cont base (append right left) displayed -> hsame meetPoint displayed := by
  intro leftCarrier rightCarrier leftRight baseMeet displayedRel
  have commutedMeet :
      Cont base (append right left) meetPoint :=
    FilterPrincipalSuffix_unary_intersection_commuted_meet_closed leftCarrier rightCarrier
      leftRight baseMeet
  exact cont_deterministic commutedMeet displayedRel

theorem FilterPrincipalSuffix_unary_intersection_zero_result_absurd
    {base left right meet leftPoint rightPoint z : BHist} :
    UnaryHistory base -> UnaryHistory left -> UnaryHistory right -> Cont left right meet ->
      Cont base left leftPoint -> Cont base right rightPoint ->
        Cont base meet (BHist.e0 z) -> False := by
  intro baseCarrier leftCarrier rightCarrier leftRight _baseLeft _baseRight baseMeet
  have meetCarrier : UnaryHistory meet := unary_cont_closed leftCarrier rightCarrier leftRight
  have resultCarrier : UnaryHistory (BHist.e0 z) :=
    unary_cont_closed baseCarrier meetCarrier baseMeet
  exact unary_no_zero_extension resultCarrier

theorem FilterPrincipalSuffix_unary_intersection_e1_result_cases
    {base left right meet leftPoint rightPoint z : BHist} :
    UnaryHistory base -> UnaryHistory left -> UnaryHistory right -> Cont left right meet ->
      Cont base left leftPoint -> Cont base right rightPoint -> Cont base meet (BHist.e1 z) ->
        (meet = BHist.Empty ∧ hsame base (BHist.e1 z)) ∨
          (exists meetTail : BHist,
            meet = BHist.e1 meetTail ∧ UnaryHistory meetTail ∧ Cont base meetTail z) := by
  intro baseCarrier leftCarrier rightCarrier leftRight _baseLeft _baseRight baseMeet
  have meetCarrier : UnaryHistory meet := unary_cont_closed leftCarrier rightCarrier leftRight
  exact unary_cont_e1_result_cases baseCarrier meetCarrier baseMeet

theorem FilterPrincipalSuffix_base_points_empty_exact
    {base left right leftPoint rightPoint : BHist} :
    Cont base left leftPoint -> Cont base right rightPoint -> hsame leftPoint BHist.Empty ->
      hsame rightPoint BHist.Empty ->
        hsame base BHist.Empty ∧ hsame left BHist.Empty ∧ hsame right BHist.Empty := by
  intro baseLeft baseRight leftPointEmpty rightPointEmpty
  cases leftPointEmpty
  cases rightPointEmpty
  have leftParts := cont_empty_result_inversion baseLeft
  have rightParts := cont_empty_result_inversion baseRight
  exact And.intro leftParts.left (And.intro leftParts.right rightParts.right)

theorem FilterPrincipalSuffix_unary_commuting_square_empty_exact
    {base left right leftPoint rightPoint lrPoint rlPoint : BHist} :
    Cont base left leftPoint -> Cont base right rightPoint -> Cont leftPoint right lrPoint ->
      Cont rightPoint left rlPoint -> hsame lrPoint BHist.Empty ->
        hsame rlPoint BHist.Empty ->
          hsame base BHist.Empty ∧ hsame left BHist.Empty ∧ hsame right BHist.Empty := by
  intro baseLeft baseRight leftThenRight rightThenLeft lrEmpty rlEmpty
  have leftThenRightEmpty : Cont leftPoint right BHist.Empty :=
    cont_result_hsame_transport leftThenRight lrEmpty
  have rightThenLeftEmpty : Cont rightPoint left BHist.Empty :=
    cont_result_hsame_transport rightThenLeft rlEmpty
  have leftParts := cont_empty_result_inversion leftThenRightEmpty
  have rightParts := cont_empty_result_inversion rightThenLeftEmpty
  exact FilterPrincipalSuffix_base_points_empty_exact baseLeft baseRight leftParts.left
    rightParts.left

theorem FilterPrincipalSuffix_intersection_empty_point_exact
    {base left right meet meetPoint : BHist} :
    Cont left right meet -> Cont base meet meetPoint -> hsame meetPoint BHist.Empty ->
      hsame base BHist.Empty ∧ hsame meet BHist.Empty ∧
        hsame left BHist.Empty ∧ hsame right BHist.Empty := by
  intro leftRight baseMeet meetPointEmpty
  cases meetPointEmpty
  have pointParts := cont_empty_result_inversion baseMeet
  cases pointParts.right
  have meetParts := cont_empty_result_inversion leftRight
  exact And.intro pointParts.left
    (And.intro (hsame_refl BHist.Empty)
      (And.intro meetParts.left meetParts.right))

theorem FilterPrincipalSuffix_intersection_empty_point_base_points_empty
    {base left right meet leftPoint rightPoint meetPoint : BHist} :
    Cont left right meet -> Cont base left leftPoint -> Cont base right rightPoint ->
      Cont base meet meetPoint -> hsame meetPoint BHist.Empty ->
        hsame leftPoint BHist.Empty ∧ hsame rightPoint BHist.Empty := by
  intro leftRight baseLeft baseRight baseMeet meetPointEmpty
  have exactness :=
    FilterPrincipalSuffix_intersection_empty_point_exact leftRight baseMeet meetPointEmpty
  constructor
  · cases baseLeft
    exact append_eq_empty_iff.mpr (And.intro exactness.left exactness.right.right.left)
  · cases baseRight
    exact append_eq_empty_iff.mpr (And.intro exactness.left exactness.right.right.right)

theorem FilterPrincipalEmptyCarrier_semanticNameCert :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty)
      (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty)
      (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty) hsame := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty (And.intro unary_empty (hsame_refl BHist.Empty))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro (unary_transport carrier.left same)
        (hsame_trans (hsame_symm same) carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

theorem FilterPrincipalVisibleCarrier_semanticNameCert_absurd {tail : BHist} :
    SemanticNameCert
      (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty ∧ hsame h (BHist.e1 tail))
      (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty ∧ hsame h (BHist.e1 tail))
      (fun h : BHist => UnaryHistory h ∧ hsame h BHist.Empty ∧ hsame h (BHist.e1 tail))
      hsame -> False := by
  intro cert
  cases semanticNameCert_ledger_policy_witness cert with
  | intro _h carrier =>
      exact not_hsame_emp_e1 (hsame_trans (hsame_symm carrier.right.left) carrier.right.right)

end BEDC.Derived.FilterUp
