import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CatLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

def CatLimitConeMor (L M D f lambda mu composite : BHist) : Prop :=
  CategoryHomCarrier L M f ∧ CategoryHomCarrier M D mu ∧
    CategoryHomCarrier L D lambda ∧ CategoryHomCarrier L D composite ∧
      Cont f mu composite ∧ hsame composite lambda

theorem CatLimitConeMor_comp_closed {L M N D f g fg lambda mu nu cLM cMN cLN : BHist} :
    CatLimitConeMor L M D f lambda mu cLM ->
      CatLimitConeMor M N D g mu nu cMN ->
        Cont f g fg -> Cont fg nu cLN ->
          CatLimitConeMor L N D fg lambda nu cLN := by
  intro left right compFG compTarget
  have fgCarrier : CategoryHomCarrier L N fg :=
    CategoryHomCarrier_comp_closed left.left right.left compFG
  have cLNCarrier : CategoryHomCarrier L D cLN :=
    CategoryHomCarrier_comp_closed fgCarrier right.right.left compTarget
  have compFCMN : Cont f cMN cLM :=
    cont_hsame_transport (hsame_refl f)
      (hsame_symm right.right.right.right.right.right) (hsame_refl cLM)
      left.right.right.right.right.left
  have sameCLNCLM : hsame cLN cLM :=
    cont_assoc_hsame compFG compTarget right.right.right.right.right.left compFCMN
  exact And.intro fgCarrier
    (And.intro right.right.left
      (And.intro left.right.right.left
        (And.intro cLNCarrier
            (And.intro compTarget
            (hsame_trans sameCLNCLM left.right.right.right.right.right)))))

theorem CatLimitConeMor_identity {L D lambda : BHist} :
    CategoryHomCarrier L D lambda ->
      CatLimitConeMor L L D BHist.Empty lambda lambda lambda := by
  intro component
  exact And.intro (CategoryHomCarrier_empty_identity component.left)
    (And.intro component
        (And.intro component
          (And.intro component
            (And.intro (cont_left_unit lambda) (hsame_refl lambda)))))

theorem CatLimitConeMor_empty_identity {L D lambda : BHist} :
    CategoryHomCarrier L D lambda ->
      CatLimitConeMor L L D BHist.Empty lambda lambda lambda := by
  intro carrier
  exact And.intro (CategoryHomCarrier_empty_identity carrier.left)
    (And.intro carrier
      (And.intro carrier
        (And.intro carrier
          (And.intro (cont_left_unit lambda) (hsame_refl lambda)))))

theorem CatLimitConeMor_identity_comparison {L D lambda : BHist} :
    CategoryHomCarrier L D lambda -> CatLimitConeMor L L D BHist.Empty lambda lambda lambda := by
  intro componentCarrier
  exact And.intro (CategoryHomCarrier_empty_identity componentCarrier.left)
    (And.intro componentCarrier
      (And.intro componentCarrier
        (And.intro componentCarrier
          (And.intro (cont_left_unit lambda) (hsame_refl lambda)))))

def CatLimitLimCone (L D lambda : BHist) : Prop :=
  CategoryHomCarrier L D lambda ∧
    (∀ {X chi : BHist}, CategoryHomCarrier X D chi ->
      ∃ m composite : BHist, CatLimitConeMor X L D m chi lambda composite) ∧
      (∀ {X chi m n cm cn : BHist}, CatLimitConeMor X L D m chi lambda cm ->
        CatLimitConeMor X L D n chi lambda cn -> hsame m n)

theorem CatLimitLimCone_endomorphism_rigidity {L D lambda a composite : BHist} :
    CatLimitLimCone L D lambda ->
      CatLimitConeMor L L D a lambda lambda composite -> hsame a BHist.Empty := by
  intro limit cone
  have idCone : CatLimitConeMor L L D BHist.Empty lambda lambda lambda :=
    CatLimitConeMor_identity limit.left
  exact limit.right.right cone idCone

theorem CatLimitLimCone_comparison_identities {L L' D lambda lambda' : BHist} :
    CatLimitLimCone L D lambda -> CatLimitLimCone L' D lambda' ->
      ∃ u v cL cL' cu cv : BHist,
        CatLimitConeMor L L' D u lambda lambda' cu ∧
          CatLimitConeMor L' L D v lambda' lambda cv ∧
            Cont u v cL ∧ Cont v u cL' ∧
              hsame cL BHist.Empty ∧ hsame cL' BHist.Empty := by
  intro leftLimit rightLimit
  cases rightLimit.right.left leftLimit.left with
  | intro u uWitness =>
      cases uWitness with
      | intro cu uCone =>
          cases leftLimit.right.left rightLimit.left with
          | intro v vWitness =>
              cases vWitness with
              | intro cv vCone =>
                  let cL := append u v
                  let cL' := append v u
                  let cTarget := append cL lambda
                  let cTarget' := append cL' lambda'
                  have uvRel : Cont u v cL := cont_intro rfl
                  have vuRel : Cont v u cL' := cont_intro rfl
                  have cTargetRel : Cont cL lambda cTarget := cont_intro rfl
                  have cTargetRel' : Cont cL' lambda' cTarget' := cont_intro rfl
                  have uvCone : CatLimitConeMor L L D cL lambda lambda cTarget :=
                    CatLimitConeMor_comp_closed uCone vCone uvRel cTargetRel
                  have vuCone : CatLimitConeMor L' L' D cL' lambda' lambda' cTarget' :=
                    CatLimitConeMor_comp_closed vCone uCone vuRel cTargetRel'
                  have idCone : CatLimitConeMor L L D BHist.Empty lambda lambda lambda :=
                    And.intro (CategoryHomCarrier_empty_identity leftLimit.left.left)
                      (And.intro leftLimit.left
                        (And.intro leftLimit.left
                          (And.intro leftLimit.left
                            (And.intro (cont_left_unit lambda) (hsame_refl lambda)))))
                  have idCone' : CatLimitConeMor L' L' D BHist.Empty lambda' lambda' lambda' :=
                    And.intro (CategoryHomCarrier_empty_identity rightLimit.left.left)
                      (And.intro rightLimit.left
                        (And.intro rightLimit.left
                          (And.intro rightLimit.left
                            (And.intro (cont_left_unit lambda') (hsame_refl lambda')))))
                  have uvEmpty : hsame cL BHist.Empty :=
                    leftLimit.right.right uvCone idCone
                  have vuEmpty : hsame cL' BHist.Empty :=
                    rightLimit.right.right vuCone idCone'
                  exact Exists.intro u
                    (Exists.intro v
                      (Exists.intro cL
                        (Exists.intro cL'
                          (Exists.intro cu
                            (Exists.intro cv
                              (And.intro uCone
                                (And.intro vCone
                                  (And.intro uvRel
                                    (And.intro vuRel
                                      (And.intro uvEmpty vuEmpty))))))))))

theorem CatLimitLimCone_comparison_fiber_collapse
    {L L' D lambda lambda' u1 u2 v1 v2 cu1 cu2 cv1 cv2 : BHist} :
    CatLimitLimCone L D lambda -> CatLimitLimCone L' D lambda' ->
      CatLimitConeMor L L' D u1 lambda lambda' cu1 ->
        CatLimitConeMor L L' D u2 lambda lambda' cu2 ->
          CatLimitConeMor L' L D v1 lambda' lambda cv1 ->
            CatLimitConeMor L' L D v2 lambda' lambda cv2 ->
              hsame u1 u2 ∧ hsame v1 v2 ∧ UnaryHistory u1 ∧ UnaryHistory v1 := by
  intro leftLimit rightLimit u1Cone u2Cone v1Cone v2Cone
  exact And.intro (rightLimit.right.right u1Cone u2Cone)
    (And.intro (leftLimit.right.right v1Cone v2Cone)
      (And.intro u1Cone.left.right.right.left v1Cone.left.right.right.left))

theorem CatLimitConeMor_nattrans_whiskering_descent
    {L M D E f lambda mu alpha lambdaAlpha muAlpha d s : BHist} :
    CatLimitConeMor L M D f lambda mu d -> CategoryHomCarrier D E alpha ->
      Cont lambda alpha lambdaAlpha -> Cont mu alpha muAlpha -> Cont f muAlpha s ->
        CatLimitConeMor L M E f lambdaAlpha muAlpha s := by
  intro cone alphaCarrier lambdaAlphaRel muAlphaRel targetRel
  have muAlphaCarrier : CategoryHomCarrier M E muAlpha :=
    CategoryHomCarrier_comp_closed cone.right.left alphaCarrier muAlphaRel
  have lambdaAlphaCarrier : CategoryHomCarrier L E lambdaAlpha :=
    CategoryHomCarrier_comp_closed cone.right.right.left alphaCarrier lambdaAlphaRel
  have targetCarrier : CategoryHomCarrier L E s :=
    CategoryHomCarrier_comp_closed cone.left muAlphaCarrier targetRel
  have dAlphaRel : Cont d alpha lambdaAlpha :=
    cont_hsame_transport (hsame_symm cone.right.right.right.right.right)
      (hsame_refl alpha) (hsame_refl lambdaAlpha) lambdaAlphaRel
  have sameLambdaAlphaTarget : hsame lambdaAlpha s :=
    cont_assoc_hsame cone.right.right.right.right.left dAlphaRel muAlphaRel targetRel
  exact And.intro cone.left
    (And.intro muAlphaCarrier
      (And.intro lambdaAlphaCarrier
        (And.intro targetCarrier
          (And.intro targetRel (hsame_symm sameLambdaAlphaTarget)))))

theorem CatLimitLimCone_transport_pointwise_equiv {L D E lambda lambdaE alpha beta : BHist} :
    CatLimitLimCone L D lambda -> CategoryHomCarrier D E alpha ->
      CategoryHomCarrier E D beta -> Cont lambda alpha lambdaE ->
        hsame (append alpha beta) BHist.Empty -> hsame (append beta alpha) BHist.Empty ->
          CatLimitLimCone L E lambdaE := by
  intro limit alphaCarrier _betaCarrier lambdaAlpha alphaBetaEmpty _betaAlphaEmpty
  have alphaEmpty : alpha = BHist.Empty := (append_eq_empty_iff.mp alphaBetaEmpty).left
  cases alphaEmpty
  have sameED : hsame E D := cont_deterministic alphaCarrier.right.right.right (cont_right_unit D)
  cases sameED
  cases lambdaAlpha
  exact limit

end BEDC.Derived.CatLimitUp
