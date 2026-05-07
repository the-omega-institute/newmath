import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LieAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.VecSpaceUp

def LieAlgebraAdjointAction (acting endpoint result : BHist) : Prop :=
  UnaryHistory acting ∧ UnaryHistory endpoint ∧ Cont acting endpoint result ∧ UnaryHistory result

theorem LieAlgebraAdjointAction_additive_linearity
    {acting y z yz left actionY actionZ rhs : BHist} :
    hsame acting BHist.Empty ->
      UnaryHistory y ->
        UnaryHistory z ->
          Cont y z yz ->
            LieAlgebraAdjointAction acting yz left ->
              LieAlgebraAdjointAction acting y actionY ->
                LieAlgebraAdjointAction acting z actionZ ->
                  Cont actionY actionZ rhs ->
                    hsame left rhs ∧ UnaryHistory left ∧ UnaryHistory rhs := by
  intro actingEmpty yUnary zUnary yzRow leftAction actionYAction actionZAction rhsRow
  have yzUnary : UnaryHistory yz := unary_cont_closed yUnary zUnary yzRow
  have leftRow : Cont acting yz left := leftAction.right.right.left
  have actionYRow : Cont acting y actionY := actionYAction.right.right.left
  have actionZRow : Cont acting z actionZ := actionZAction.right.right.left
  have sameLeftYZ : hsame left yz := by
    cases actingEmpty
    exact cont_left_unit_result leftRow
  have sameActionY : hsame actionY y := by
    cases actingEmpty
    exact cont_left_unit_result actionYRow
  have sameActionZ : hsame actionZ z := by
    cases actingEmpty
    exact cont_left_unit_result actionZRow
  have sameRhsYZ : hsame rhs yz :=
    cont_respects_hsame sameActionY sameActionZ rhsRow yzRow
  have rhsUnary : UnaryHistory rhs := unary_transport yzUnary (hsame_symm sameRhsYZ)
  exact And.intro (hsame_trans sameLeftYZ (hsame_symm sameRhsYZ))
    (And.intro leftAction.right.right.right rhsUnary)

def LieAlgebraSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def LieAlgebraSingletonBracket (x y : BHist) : BHist :=
  append x y

theorem LieAlgebraSingletonAdjoint_additive_linearity {x y z yz left right : BHist} :
    LieAlgebraSingletonCarrier x -> LieAlgebraSingletonCarrier y ->
      LieAlgebraSingletonCarrier z -> Cont y z yz -> Cont x yz left ->
        Cont (LieAlgebraSingletonBracket x y) (LieAlgebraSingletonBracket x z) right ->
          hsame left right ∧ LieAlgebraSingletonCarrier left ∧
            LieAlgebraSingletonCarrier right ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro carrierX carrierY carrierZ yzRow leftRow rightRow
  have yzEmpty : hsame yz BHist.Empty :=
    cont_respects_hsame carrierY carrierZ yzRow (cont_left_unit BHist.Empty)
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame carrierX yzEmpty leftRow (cont_left_unit BHist.Empty)
  have bracketXYEmpty : hsame (LieAlgebraSingletonBracket x y) BHist.Empty := by
    exact append_eq_empty_iff.mpr (And.intro carrierX carrierY)
  have bracketXZEmpty : hsame (LieAlgebraSingletonBracket x z) BHist.Empty := by
    exact append_eq_empty_iff.mpr (And.intro carrierX carrierZ)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame bracketXYEmpty bracketXZEmpty rightRow (cont_left_unit BHist.Empty)
  have sameLeftRight : hsame left right :=
    hsame_trans leftEmpty (hsame_symm rightEmpty)
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro sameLeftRight
    (And.intro leftEmpty (And.intro rightEmpty (And.intro leftUnary rightUnary)))

def LieAlgebraSingletonAdjointAction (x t : BHist) : BHist :=
  append x t

theorem LieAlgebraSingleton_adjoint_action_additive_linearity
    {x y z yz left xy xz right : BHist} :
    VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier y -> VecSpaceSingletonCarrier z ->
      Cont y z yz -> Cont x yz left -> Cont x y xy -> Cont x z xz ->
        Cont xy xz right -> VecSpaceSingletonClassifier left right := by
  intro carrierX carrierY carrierZ yzRow leftRow xyRow xzRow rightRow
  have yzEmpty : hsame yz BHist.Empty := by
    cases carrierY
    cases carrierZ
    cases yzRow
    rfl
  have leftEmpty : hsame left BHist.Empty := by
    cases carrierX
    cases yzEmpty
    cases leftRow
    rfl
  have xyEmpty : hsame xy BHist.Empty := by
    cases carrierX
    cases carrierY
    cases xyRow
    rfl
  have xzEmpty : hsame xz BHist.Empty := by
    cases carrierX
    cases carrierZ
    cases xzRow
    rfl
  have rightEmpty : hsame right BHist.Empty := by
    cases xyEmpty
    cases xzEmpty
    cases rightRow
    rfl
  exact And.intro leftEmpty
    (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem LieAlgebraSingletonAdjoint_scalar_endpoint_closure {r x y ry left xy right : BHist} :
    VecSpaceSingletonCarrier r -> VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier y ->
      Cont r y ry -> Cont x ry left -> Cont x y xy -> Cont r xy right ->
        VecSpaceSingletonClassifier left right ∧ VecSpaceSingletonCarrier left ∧
          VecSpaceSingletonCarrier right ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro carrierR carrierX carrierY ryRow leftRow xyRow rightRow
  have ryEmpty : hsame ry BHist.Empty :=
    cont_respects_hsame carrierR carrierY ryRow (cont_left_unit BHist.Empty)
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame carrierX ryEmpty leftRow (cont_left_unit BHist.Empty)
  have xyEmpty : hsame xy BHist.Empty :=
    cont_respects_hsame carrierX carrierY xyRow (cont_left_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame carrierR xyEmpty rightRow (cont_left_unit BHist.Empty)
  have leftRight : VecSpaceSingletonClassifier left right :=
    And.intro leftEmpty
      (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro leftRight
    (And.intro leftEmpty (And.intro rightEmpty (And.intro leftUnary rightUnary)))

theorem LieAlgebraSingletonAdjoint_commutator_identity
    {x y z yz xy xz x_yz y_xz commutator target : BHist} :
    LieAlgebraSingletonCarrier x -> LieAlgebraSingletonCarrier y ->
      LieAlgebraSingletonCarrier z -> Cont y z yz -> Cont x y xy -> Cont x z xz ->
        Cont x yz x_yz -> Cont y xz y_xz -> Cont x_yz y_xz commutator ->
          Cont xy z target ->
            hsame commutator target ∧ LieAlgebraSingletonCarrier commutator ∧
              LieAlgebraSingletonCarrier target ∧ UnaryHistory commutator ∧
                UnaryHistory target := by
  intro carrierX carrierY carrierZ yzRow xyRow xzRow xYzRow yXzRow commutatorRow targetRow
  have yzEmpty : hsame yz BHist.Empty :=
    cont_respects_hsame carrierY carrierZ yzRow (cont_left_unit BHist.Empty)
  have xyEmpty : hsame xy BHist.Empty :=
    cont_respects_hsame carrierX carrierY xyRow (cont_left_unit BHist.Empty)
  have xzEmpty : hsame xz BHist.Empty :=
    cont_respects_hsame carrierX carrierZ xzRow (cont_left_unit BHist.Empty)
  have xYzEmpty : hsame x_yz BHist.Empty :=
    cont_respects_hsame carrierX yzEmpty xYzRow (cont_left_unit BHist.Empty)
  have yXzEmpty : hsame y_xz BHist.Empty :=
    cont_respects_hsame carrierY xzEmpty yXzRow (cont_left_unit BHist.Empty)
  have commutatorEmpty : hsame commutator BHist.Empty :=
    cont_respects_hsame xYzEmpty yXzEmpty commutatorRow (cont_left_unit BHist.Empty)
  have targetEmpty : hsame target BHist.Empty :=
    cont_respects_hsame xyEmpty carrierZ targetRow (cont_left_unit BHist.Empty)
  have sameCommutatorTarget : hsame commutator target :=
    hsame_trans commutatorEmpty (hsame_symm targetEmpty)
  have commutatorUnary : UnaryHistory commutator :=
    unary_transport unary_empty (hsame_symm commutatorEmpty)
  have targetUnary : UnaryHistory target :=
    unary_transport unary_empty (hsame_symm targetEmpty)
  exact And.intro sameCommutatorTarget
    (And.intro commutatorEmpty
      (And.intro targetEmpty (And.intro commutatorUnary targetUnary)))

protected theorem LieAlgebraSingletonAdjoint_derivation_from_jacobi
    {x y z yz xy xz left rightLeft rightRight rhs : BHist} :
    LieAlgebraSingletonCarrier x -> LieAlgebraSingletonCarrier y ->
      LieAlgebraSingletonCarrier z -> Cont y z yz -> Cont x y xy -> Cont x z xz ->
        Cont x yz left -> Cont xy z rightLeft -> Cont y xz rightRight ->
          Cont rightLeft rightRight rhs ->
            hsame left rhs ∧ LieAlgebraSingletonCarrier left ∧
              LieAlgebraSingletonCarrier rhs ∧ UnaryHistory left ∧ UnaryHistory rhs := by
  intro carrierX carrierY carrierZ yzRow xyRow xzRow leftRow rightLeftRow rightRightRow rhsRow
  have yzEmpty : hsame yz BHist.Empty :=
    cont_respects_hsame carrierY carrierZ yzRow (cont_left_unit BHist.Empty)
  have xyEmpty : hsame xy BHist.Empty :=
    cont_respects_hsame carrierX carrierY xyRow (cont_left_unit BHist.Empty)
  have xzEmpty : hsame xz BHist.Empty :=
    cont_respects_hsame carrierX carrierZ xzRow (cont_left_unit BHist.Empty)
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame carrierX yzEmpty leftRow (cont_left_unit BHist.Empty)
  have rightLeftEmpty : hsame rightLeft BHist.Empty :=
    cont_respects_hsame xyEmpty carrierZ rightLeftRow (cont_left_unit BHist.Empty)
  have rightRightEmpty : hsame rightRight BHist.Empty :=
    cont_respects_hsame carrierY xzEmpty rightRightRow (cont_left_unit BHist.Empty)
  have rhsEmpty : hsame rhs BHist.Empty :=
    cont_respects_hsame rightLeftEmpty rightRightEmpty rhsRow (cont_left_unit BHist.Empty)
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rhsUnary : UnaryHistory rhs :=
    unary_transport unary_empty (hsame_symm rhsEmpty)
  exact And.intro (hsame_trans leftEmpty (hsame_symm rhsEmpty))
    (And.intro leftEmpty (And.intro rhsEmpty (And.intro leftUnary rhsUnary)))

theorem LieAlgebraSingletonAdjoint_scalar_linearity {r x y left xy right : BHist} :
    VecSpaceSingletonCarrier r -> VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier y ->
      Cont x (VecSpaceSingletonSmul r y) left -> Cont x y xy -> Cont r xy right ->
        VecSpaceSingletonClassifier left right ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro carrierR carrierX carrierY leftRow xyRow rightRow
  have smulEmpty : hsame (VecSpaceSingletonSmul r y) BHist.Empty :=
    hsame_refl BHist.Empty
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame carrierX smulEmpty leftRow (cont_left_unit BHist.Empty)
  have xyEmpty : hsame xy BHist.Empty :=
    cont_respects_hsame carrierX carrierY xyRow (cont_left_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame carrierR xyEmpty rightRow (cont_left_unit BHist.Empty)
  have classified : VecSpaceSingletonClassifier left right :=
    And.intro leftEmpty (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro classified (And.intro leftUnary rightUnary)

theorem LieAlgebraSingletonAdjoint_acting_endpoint_additive_linearity
    {x z y xz left xy zy right : BHist} :
    VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier z -> VecSpaceSingletonCarrier y ->
      Cont x z xz -> Cont xz y left -> Cont x y xy -> Cont z y zy -> Cont xy zy right ->
        VecSpaceSingletonClassifier left right ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro carrierX carrierZ carrierY xzRow leftRow xyRow zyRow rightRow
  have xzEmpty : hsame xz BHist.Empty :=
    cont_respects_hsame carrierX carrierZ xzRow (cont_left_unit BHist.Empty)
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame xzEmpty carrierY leftRow (cont_left_unit BHist.Empty)
  have xyEmpty : hsame xy BHist.Empty :=
    cont_respects_hsame carrierX carrierY xyRow (cont_left_unit BHist.Empty)
  have zyEmpty : hsame zy BHist.Empty :=
    cont_respects_hsame carrierZ carrierY zyRow (cont_left_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame xyEmpty zyEmpty rightRow (cont_left_unit BHist.Empty)
  have classified : VecSpaceSingletonClassifier left right :=
    And.intro leftEmpty (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro classified (And.intro leftUnary rightUnary)

theorem LieAlgebraSingletonAdjoint_acting_endpoint_additive_linearity_classifier
    {x z y xz left xy zy right : BHist} :
    VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier z -> VecSpaceSingletonCarrier y ->
      Cont x z xz -> Cont xz y left -> Cont x y xy -> Cont z y zy ->
        Cont xy zy right -> VecSpaceSingletonClassifier left right := by
  intro carrierX carrierZ carrierY xzRow leftRow xyRow zyRow rightRow
  exact (LieAlgebraSingletonAdjoint_acting_endpoint_additive_linearity
    carrierX carrierZ carrierY xzRow leftRow xyRow zyRow rightRow).left

theorem LieAlgebraSingletonAdjoint_acting_endpoint_scalar_linearity
    {r x y smulX left xy right : BHist} :
    VecSpaceSingletonCarrier r -> VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier y ->
      Cont r x smulX -> Cont smulX y left -> Cont x y xy -> Cont r xy right ->
        VecSpaceSingletonClassifier left right ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro carrierR carrierX carrierY smulXRow leftRow xyRow rightRow
  have smulXEmpty : hsame smulX BHist.Empty :=
    cont_respects_hsame carrierR carrierX smulXRow (cont_left_unit BHist.Empty)
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame smulXEmpty carrierY leftRow (cont_left_unit BHist.Empty)
  have xyEmpty : hsame xy BHist.Empty :=
    cont_respects_hsame carrierX carrierY xyRow (cont_left_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame carrierR xyEmpty rightRow (cont_left_unit BHist.Empty)
  have classified : VecSpaceSingletonClassifier left right :=
    And.intro leftEmpty (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro classified (And.intro leftUnary rightUnary)

theorem LieAlgebraSingletonBracket_left_zero_annihilation {x left right : BHist} :
    LieAlgebraSingletonCarrier x ->
      Cont BHist.Empty x left -> Cont x BHist.Empty right ->
        LieAlgebraSingletonCarrier left ∧ LieAlgebraSingletonCarrier right ∧
          VecSpaceSingletonClassifier left BHist.Empty ∧
          VecSpaceSingletonClassifier right BHist.Empty ∧
          hsame left right ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro carrierX leftRow rightRow
  have leftEmpty : hsame left BHist.Empty :=
    hsame_trans (cont_left_unit_result leftRow) carrierX
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame carrierX (hsame_refl BHist.Empty) rightRow (cont_left_unit BHist.Empty)
  have leftClassified : VecSpaceSingletonClassifier left BHist.Empty :=
    And.intro leftEmpty
      (And.intro (hsame_refl BHist.Empty) leftEmpty)
  have rightClassified : VecSpaceSingletonClassifier right BHist.Empty :=
    And.intro rightEmpty
      (And.intro (hsame_refl BHist.Empty) rightEmpty)
  have sameLeftRight : hsame left right :=
    hsame_trans leftEmpty (hsame_symm rightEmpty)
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro leftEmpty
    (And.intro rightEmpty
      (And.intro leftClassified
        (And.intro rightClassified
          (And.intro sameLeftRight (And.intro leftUnary rightUnary)))))

theorem LieAlgebraSingletonAdjoint_endomap_package
    {x y z yz addLeft xy xz addRight r scalarLeft scalarRight zeroImage : BHist} :
    VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier y -> VecSpaceSingletonCarrier z ->
      VecSpaceSingletonCarrier r -> Cont y z yz -> Cont x yz addLeft -> Cont x y xy ->
        Cont x z xz -> Cont xy xz addRight -> Cont x (VecSpaceSingletonSmul r y) scalarLeft ->
          Cont r xy scalarRight -> Cont x BHist.Empty zeroImage ->
            VecSpaceSingletonClassifier addLeft addRight ∧
              VecSpaceSingletonClassifier scalarLeft scalarRight ∧
              VecSpaceSingletonClassifier zeroImage BHist.Empty ∧ UnaryHistory addLeft ∧
                UnaryHistory addRight ∧ UnaryHistory scalarLeft ∧ UnaryHistory scalarRight ∧
                  UnaryHistory zeroImage := by
  intro carrierX carrierY carrierZ carrierR yzRow addLeftRow xyRow xzRow addRightRow
  intro scalarLeftRow scalarRightRow zeroRow
  have additiveRows :=
    LieAlgebraSingleton_adjoint_action_additive_linearity carrierX carrierY carrierZ yzRow
      addLeftRow xyRow xzRow addRightRow
  have scalarRows :=
    LieAlgebraSingletonAdjoint_scalar_linearity carrierR carrierX carrierY scalarLeftRow xyRow
      scalarRightRow
  have zeroEmpty : VecSpaceSingletonCarrier zeroImage :=
    cont_respects_hsame carrierX (hsame_refl BHist.Empty) zeroRow (cont_left_unit BHist.Empty)
  have zeroClassified : VecSpaceSingletonClassifier zeroImage BHist.Empty :=
    And.intro zeroEmpty (And.intro (hsame_refl BHist.Empty) zeroEmpty)
  have xUnary : UnaryHistory x := unary_transport unary_empty (hsame_symm carrierX)
  have yUnary : UnaryHistory y := unary_transport unary_empty (hsame_symm carrierY)
  have zUnary : UnaryHistory z := unary_transport unary_empty (hsame_symm carrierZ)
  have rUnary : UnaryHistory r := unary_transport unary_empty (hsame_symm carrierR)
  have yzUnary : UnaryHistory yz := unary_cont_closed yUnary zUnary yzRow
  have xyUnary : UnaryHistory xy := unary_cont_closed xUnary yUnary xyRow
  have xzUnary : UnaryHistory xz := unary_cont_closed xUnary zUnary xzRow
  have addLeftUnary : UnaryHistory addLeft := unary_cont_closed xUnary yzUnary addLeftRow
  have addRightUnary : UnaryHistory addRight := unary_cont_closed xyUnary xzUnary addRightRow
  have scalarLeftUnary : UnaryHistory scalarLeft :=
    unary_cont_closed xUnary unary_empty scalarLeftRow
  have scalarRightUnary : UnaryHistory scalarRight :=
    unary_cont_closed rUnary xyUnary scalarRightRow
  have zeroUnary : UnaryHistory zeroImage :=
    unary_transport unary_empty (hsame_symm zeroEmpty)
  exact And.intro additiveRows
    (And.intro scalarRows.left
      (And.intro zeroClassified
        (And.intro addLeftUnary
          (And.intro addRightUnary
            (And.intro scalarLeftUnary
              (And.intro scalarRightUnary zeroUnary))))))

end BEDC.Derived.LieAlgebraUp
