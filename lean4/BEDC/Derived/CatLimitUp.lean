import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CatLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

def CatLimitLimCone (L D lambda : BHist) : Prop :=
  CategoryHomCarrier L D lambda ∧
    (∀ {X chi : BHist}, CategoryHomCarrier X D chi ->
      ∃ m composite : BHist, CatLimitConeMor X L D m chi lambda composite) ∧
      (∀ {X chi m n cm cn : BHist}, CatLimitConeMor X L D m chi lambda cm ->
        CatLimitConeMor X L D n chi lambda cn -> hsame m n)

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

end BEDC.Derived.CatLimitUp
