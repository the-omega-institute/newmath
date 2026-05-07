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

theorem PreSheafIndexedRestrictionSurface_section_restriction_transport
    {sec rho identity composite sec' rho' identity' composite' : BHist} :
    PreSheafIndexedRestrictionSurface sec rho identity composite ->
      hsame sec sec' -> hsame rho rho' -> Cont sec' rho' identity' ->
        Cont rho' identity' composite' ->
          PreSheafIndexedRestrictionSurface sec' rho' identity' composite' ∧
            hsame identity identity' ∧ hsame composite composite' ∧
              UnaryHistory identity' ∧ UnaryHistory composite' := by
  intro surface sameSec sameRho identityCont' compositeCont'
  have secUnary' : UnaryHistory sec' :=
    unary_transport surface.left sameSec
  have rhoUnary' : UnaryHistory rho' :=
    unary_transport surface.right.left sameRho
  have identityUnary' : UnaryHistory identity' :=
    unary_cont_closed secUnary' rhoUnary' identityCont'
  have sameIdentity : hsame identity identity' :=
    cont_respects_hsame sameSec sameRho surface.right.right.left identityCont'
  have compositeUnary' : UnaryHistory composite' :=
    unary_cont_closed rhoUnary' identityUnary' compositeCont'
  have sameComposite : hsame composite composite' :=
    cont_respects_hsame sameRho sameIdentity surface.right.right.right compositeCont'
  exact And.intro
    (And.intro secUnary'
      (And.intro rhoUnary' (And.intro identityCont' compositeCont')))
    (And.intro sameIdentity
      (And.intro sameComposite (And.intro identityUnary' compositeUnary')))

end BEDC.Derived.PreSheafUp
