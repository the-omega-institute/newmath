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

theorem CatColimitCoconeMor_identity {D K kappa : BHist} :
    CategoryHomCarrier D K kappa ->
      CatColimitCoconeMor D K K kappa kappa BHist.Empty kappa := by
  intro component
  exact And.intro (CategoryHomCarrier_empty_identity component.right.left)
    (And.intro component
      (And.intro component
        (And.intro component
          (And.intro (cont_right_unit kappa) (hsame_refl kappa)))))

end BEDC.Derived.CatColimitUp
