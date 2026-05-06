import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CatColimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.CategoryUp

def CatColimitCoconeMor (D K M kappa mu f composite : BHist) : Prop :=
  CategoryHomCarrier K M f ∧ CategoryHomCarrier D K kappa ∧
    CategoryHomCarrier D M mu ∧ CategoryHomCarrier D M composite ∧
      Cont kappa f composite ∧ hsame composite mu

theorem CatColimitCoconeMor_comp_closed {D K M N kappa mu nu f g fg cKM cMN cKN : BHist} :
    CatColimitCoconeMor D K M kappa mu f cKM ->
      CatColimitCoconeMor D M N mu nu g cMN ->
        Cont f g fg -> Cont kappa fg cKN ->
          CatColimitCoconeMor D K N kappa nu fg cKN := by
  intro left right compFG compSource
  have fgCarrier : CategoryHomCarrier K N fg :=
    CategoryHomCarrier_comp_closed left.left right.left compFG
  have cKNCarrier : CategoryHomCarrier D N cKN :=
    CategoryHomCarrier_comp_closed left.right.left fgCarrier compSource
  have compCKMG : Cont cKM g cMN :=
    cont_hsame_transport (hsame_symm left.right.right.right.right.right)
      (hsame_refl g) (hsame_refl cMN) right.right.right.right.right.left
  have sameCMNCKN : hsame cMN cKN :=
    cont_assoc_hsame left.right.right.right.right.left compCKMG compFG compSource
  exact And.intro fgCarrier
    (And.intro left.right.left
      (And.intro right.right.right.left
        (And.intro cKNCarrier
          (And.intro compSource
            (hsame_trans (hsame_symm sameCMNCKN) right.right.right.right.right.right)))))

theorem CatColimitCoconeMor_nattrans_prewhiskering_descent
    {D E K M beta kappa mu kappaBeta muBeta f d s : BHist} :
    CatColimitCoconeMor D K M kappa mu f d -> CategoryHomCarrier E D beta ->
      Cont beta kappa kappaBeta -> Cont beta mu muBeta -> Cont kappaBeta f s ->
        CatColimitCoconeMor E K M kappaBeta muBeta f s := by
  intro cocone betaCarrier kappaBetaRel muBetaRel sourceRel
  have kappaBetaCarrier : CategoryHomCarrier E K kappaBeta :=
    CategoryHomCarrier_comp_closed betaCarrier cocone.right.left kappaBetaRel
  have muBetaCarrier : CategoryHomCarrier E M muBeta :=
    CategoryHomCarrier_comp_closed betaCarrier cocone.right.right.left muBetaRel
  have sourceCarrier : CategoryHomCarrier E M s :=
    CategoryHomCarrier_comp_closed kappaBetaCarrier cocone.left sourceRel
  have betaDRel : Cont beta d muBeta :=
    cont_hsame_transport (hsame_refl beta)
      (hsame_symm cocone.right.right.right.right.right) (hsame_refl muBeta)
      muBetaRel
  have sameSMuBeta : hsame s muBeta :=
    cont_assoc_hsame kappaBetaRel sourceRel cocone.right.right.right.right.left betaDRel
  exact And.intro cocone.left
    (And.intro kappaBetaCarrier
      (And.intro muBetaCarrier
        (And.intro sourceCarrier
          (And.intro sourceRel sameSMuBeta))))

end BEDC.Derived.CatColimitUp
