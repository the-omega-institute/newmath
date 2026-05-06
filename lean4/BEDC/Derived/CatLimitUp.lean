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

theorem CatLimitConeMor_identity_comparison {L D lambda : BHist} :
    CategoryHomCarrier L D lambda -> CatLimitConeMor L L D BHist.Empty lambda lambda lambda := by
  intro componentCarrier
  exact And.intro (CategoryHomCarrier_empty_identity componentCarrier.left)
    (And.intro componentCarrier
      (And.intro componentCarrier
        (And.intro componentCarrier
          (And.intro (cont_left_unit lambda) (hsame_refl lambda)))))

end BEDC.Derived.CatLimitUp
