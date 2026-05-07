import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.PreSheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def PreSheafIndexedRestrictionSurface
    (sec rho identity composite : BHist) : Prop :=
  UnaryHistory sec ∧ UnaryHistory rho ∧ Cont sec rho identity ∧ Cont rho identity composite

theorem PreSheafIndexedRestrictionSurface_functoriality_surface
    {sec rho identity composite identity' composite' : BHist} :
    PreSheafIndexedRestrictionSurface sec rho identity composite ->
      hsame identity identity' -> Cont rho identity' composite' ->
        PreSheafIndexedRestrictionSurface sec rho identity' composite' ∧
          hsame composite composite' ∧ UnaryHistory composite' := by
  intro surface sameIdentity compositeCont'
  have identityCont' : Cont sec rho identity' :=
    cont_result_hsame_transport surface.right.right.left sameIdentity
  have identityUnary' : UnaryHistory identity' :=
    unary_cont_closed surface.left surface.right.left identityCont'
  have compositeUnary' : UnaryHistory composite' :=
    unary_cont_closed surface.right.left identityUnary' compositeCont'
  have sameComposite : hsame composite composite' :=
    cont_respects_hsame (hsame_refl rho) sameIdentity surface.right.right.right
      compositeCont'
  exact And.intro
    (And.intro surface.left (And.intro surface.right.left
      (And.intro identityCont' compositeCont')))
    (And.intro sameComposite compositeUnary')

end BEDC.Derived.PreSheafUp
