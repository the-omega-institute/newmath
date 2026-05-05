import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.FilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ContinuousUp
open BEDC.Derived.ContinuousMapUp

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

theorem ContinuousMapCarrier_principal_suffix_point_determinacy
    {base map target modulus cert distance suffix sourcePoint targetPoint target0 target1
      modulus0 modulus1 cert0 cert1 distance0 distance1 : BHist} :
    ContinuousMapCarrier base map target modulus cert distance -> UnaryHistory suffix ->
      Cont base suffix sourcePoint -> Cont target suffix targetPoint ->
        ContinuousMapCarrier sourcePoint map target0 modulus0 cert0 distance0 ->
          ContinuousMapCarrier sourcePoint map target1 modulus1 cert1 distance1 ->
            hsame target0 target1 ∧ hsame targetPoint target0 ∧ hsame targetPoint target1 := by
  intro baseCarrier suffixCarrier baseSuffix targetSuffix image0 image1
  have mapCarrier : UnaryHistory map := baseCarrier.left.right.right.left
  have baseMap : Cont base map target := baseCarrier.left.right.right.right.right.left
  have sourceMap0 : Cont sourcePoint map target0 := image0.left.right.right.right.right.left
  have sourceMap1 : Cont sourcePoint map target1 := image1.left.right.right.right.right.left
  have target0SameTargetPoint : hsame target0 targetPoint :=
    FilterPrincipalSuffix_unary_commuting_square suffixCarrier mapCarrier baseSuffix baseMap
      sourceMap0 targetSuffix
  have target1SameTargetPoint : hsame target1 targetPoint :=
    FilterPrincipalSuffix_unary_commuting_square suffixCarrier mapCarrier baseSuffix baseMap
      sourceMap1 targetSuffix
  exact And.intro
    (hsame_trans target0SameTargetPoint (hsame_symm target1SameTargetPoint))
    (And.intro (hsame_symm target0SameTargetPoint) (hsame_symm target1SameTargetPoint))

theorem ContinuousMap_image_principal_suffix_point_determinacy
    {base map target modulus cert distance suffix sourcePoint targetPoint target0 target1
      modulus0 modulus1 cert0 cert1 distance0 distance1 : BHist} :
    ContinuousMapCarrier base map target modulus cert distance -> UnaryHistory suffix ->
      Cont base suffix sourcePoint -> Cont target suffix targetPoint ->
        ContinuousMapCarrier sourcePoint map target0 modulus0 cert0 distance0 ->
          ContinuousMapCarrier sourcePoint map target1 modulus1 cert1 distance1 ->
            hsame target0 target1 ∧ hsame targetPoint target0 ∧ hsame targetPoint target1 := by
  intro baseCarrier suffixCarrier baseSuffix targetSuffix displayed0 displayed1
  have mapCarrier : UnaryHistory map :=
    baseCarrier.left.right.right.left
  have baseGraph : Cont base map target :=
    baseCarrier.left.right.right.right.right.left
  have displayedGraph0 : Cont sourcePoint map target0 :=
    displayed0.left.right.right.right.right.left
  have displayedGraph1 : Cont sourcePoint map target1 :=
    displayed1.left.right.right.right.right.left
  have targetPointTarget0 : hsame targetPoint target0 :=
    FilterPrincipalSuffix_unary_commuting_square mapCarrier suffixCarrier baseGraph baseSuffix
      targetSuffix displayedGraph0
  have targetPointTarget1 : hsame targetPoint target1 :=
    FilterPrincipalSuffix_unary_commuting_square mapCarrier suffixCarrier baseGraph baseSuffix
      targetSuffix displayedGraph1
  exact And.intro (hsame_trans (hsame_symm targetPointTarget0) targetPointTarget1)
    (And.intro targetPointTarget0 targetPointTarget1)

theorem FilterPrincipalSuffix_continuousMap_image_package
    {base map target modulus cert distance left right meet leftPoint rightPoint meetPoint : BHist} :
    ContinuousMapCarrier base map target modulus cert distance -> UnaryHistory left ->
      UnaryHistory right -> Cont left right meet -> Cont base left leftPoint ->
        Cont base right rightPoint -> Cont base meet meetPoint ->
          exists targetLeft targetRight targetMeet imageLeft imageRight imageMeet : BHist,
            Cont target left targetLeft ∧ Cont target right targetRight ∧
              Cont target meet targetMeet ∧ UnaryHistory targetMeet ∧
                Cont targetLeft right targetMeet ∧ Cont targetRight left targetMeet ∧
                  Cont leftPoint map imageLeft ∧ Cont rightPoint map imageRight ∧
                    Cont meetPoint map imageMeet ∧ hsame targetLeft imageLeft ∧
                      hsame targetRight imageRight ∧ hsame targetMeet imageMeet ∧
                        (forall z : BHist, Cont targetLeft right z -> hsame targetMeet z) ∧
                          (forall z : BHist,
                            Cont targetRight left z -> hsame targetMeet z) ∧
                            (forall lr rl : BHist, Cont targetLeft right lr ->
                              Cont targetRight left rl -> hsame lr rl) ∧
                              (forall z : BHist, Cont leftPoint map z -> hsame targetLeft z) ∧
                                (forall z : BHist,
                                  Cont rightPoint map z -> hsame targetRight z) ∧
                                  (forall z : BHist,
                                    Cont meetPoint map z -> hsame targetMeet z) := by
  intro carrier leftCarrier rightCarrier leftRight baseLeft baseRight baseMeet
  let targetLeft : BHist := append target left
  let targetRight : BHist := append target right
  let targetMeet : BHist := append target meet
  let imageLeft : BHist := append leftPoint map
  let imageRight : BHist := append rightPoint map
  let imageMeet : BHist := append meetPoint map
  have functionCarrier := carrier.left
  have targetCarrier : UnaryHistory target := functionCarrier.right.left
  have mapCarrier : UnaryHistory map := functionCarrier.right.right.left
  have sourceMap : Cont base map target := functionCarrier.right.right.right.right.left
  have meetCarrier : UnaryHistory meet :=
    unary_cont_closed leftCarrier rightCarrier leftRight
  have targetLeftRel : Cont target left targetLeft := by
    rfl
  have targetRightRel : Cont target right targetRight := by
    rfl
  have targetMeetRel : Cont target meet targetMeet := by
    rfl
  have imageLeftRel : Cont leftPoint map imageLeft := by
    rfl
  have imageRightRel : Cont rightPoint map imageRight := by
    rfl
  have imageMeetRel : Cont meetPoint map imageMeet := by
    rfl
  have sameTargetLeftImage : hsame targetLeft imageLeft := by
    dsimp [targetLeft, imageLeft]
    cases sourceMap
    cases baseLeft
    exact
      (append_assoc base map left).trans
        ((congrArg (append base) (unary_append_comm mapCarrier leftCarrier)).trans
          (append_assoc base left map).symm)
  have sameTargetRightImage : hsame targetRight imageRight := by
    dsimp [targetRight, imageRight]
    cases sourceMap
    cases baseRight
    exact
      (append_assoc base map right).trans
        ((congrArg (append base) (unary_append_comm mapCarrier rightCarrier)).trans
          (append_assoc base right map).symm)
  have sameTargetMeetImage : hsame targetMeet imageMeet := by
    dsimp [targetMeet, imageMeet]
    cases sourceMap
    cases baseMeet
    exact
      (append_assoc base map meet).trans
        ((congrArg (append base) (unary_append_comm mapCarrier meetCarrier)).trans
          (append_assoc base meet map).symm)
  have targetClosed :=
    FilterPrincipalSuffix_unary_intersection_closed targetCarrier leftCarrier rightCarrier
      leftRight targetLeftRel targetRightRel targetMeetRel
  refine Exists.intro targetLeft ?_
  refine Exists.intro targetRight ?_
  refine Exists.intro targetMeet ?_
  refine Exists.intro imageLeft ?_
  refine Exists.intro imageRight ?_
  refine Exists.intro imageMeet ?_
  constructor
  · exact targetLeftRel
  constructor
  · exact targetRightRel
  constructor
  · exact targetMeetRel
  constructor
  · exact targetClosed.left
  constructor
  · exact targetClosed.right.left
  constructor
  · exact targetClosed.right.right
  constructor
  · exact imageLeftRel
  constructor
  · exact imageRightRel
  constructor
  · exact imageMeetRel
  constructor
  · exact sameTargetLeftImage
  constructor
  · exact sameTargetRightImage
  constructor
  · exact sameTargetMeetImage
  constructor
  · intro z displayed
    exact cont_deterministic targetClosed.right.left displayed
  constructor
  · intro z displayed
    exact cont_deterministic targetClosed.right.right displayed
  constructor
  · intro lr rl lrRel rlRel
    exact
      FilterPrincipalSuffix_unary_commuting_square leftCarrier rightCarrier targetLeftRel
        targetRightRel lrRel rlRel
  constructor
  · intro z displayed
    exact hsame_trans sameTargetLeftImage (cont_deterministic imageLeftRel displayed)
  constructor
  · intro z displayed
    exact hsame_trans sameTargetRightImage (cont_deterministic imageRightRel displayed)
  · intro z displayed
    exact hsame_trans sameTargetMeetImage (cont_deterministic imageMeetRel displayed)

theorem FilterPrincipalSuffix_continuousMap_image_point_determinacy
    {base map target modulus cert distance suffix sourcePoint targetPoint target0 target1
        modulus0 modulus1 cert0 cert1 distance0 distance1 : BHist} :
    ContinuousMapCarrier base map target modulus cert distance -> UnaryHistory suffix ->
      Cont base suffix sourcePoint -> Cont target suffix targetPoint ->
        ContinuousMapCarrier sourcePoint map target0 modulus0 cert0 distance0 ->
          ContinuousMapCarrier sourcePoint map target1 modulus1 cert1 distance1 ->
            hsame target0 target1 ∧ hsame targetPoint target0 ∧ hsame targetPoint target1 := by
  intro baseCarrier suffixCarrier sourceSuffix targetSuffix image0 image1
  have baseReadback :=
    ContinuousFunctionCarrier_graph_modulus_cont_readback baseCarrier.left
  have image0Readback :=
    ContinuousFunctionCarrier_graph_modulus_cont_readback image0.left
  have image1Readback :=
    ContinuousFunctionCarrier_graph_modulus_cont_readback image1.left
  have mapCarrier : UnaryHistory map := baseCarrier.left.right.right.left
  have sameTarget0Point :
      hsame target0 targetPoint :=
    FilterPrincipalSuffix_unary_commuting_square suffixCarrier mapCarrier
      sourceSuffix baseReadback.left image0Readback.left targetSuffix
  have sameTarget1Point :
      hsame target1 targetPoint :=
    FilterPrincipalSuffix_unary_commuting_square suffixCarrier mapCarrier
      sourceSuffix baseReadback.left image1Readback.left targetSuffix
  exact And.intro
    (hsame_trans sameTarget0Point (hsame_symm sameTarget1Point))
    (And.intro (hsame_symm sameTarget0Point) (hsame_symm sameTarget1Point))

end BEDC.Derived.FilterUp
