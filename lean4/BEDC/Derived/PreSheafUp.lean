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

theorem PreSheafIndexedRestrictionSurface_carrier_rows {sec rho identity composite : BHist} :
    PreSheafIndexedRestrictionSurface sec rho identity composite ->
      UnaryHistory sec ∧ UnaryHistory rho ∧ UnaryHistory identity ∧
        UnaryHistory composite ∧ Cont sec rho identity ∧ Cont rho identity composite := by
  intro surface
  have identityUnary : UnaryHistory identity :=
    unary_cont_closed surface.left surface.right.left surface.right.right.left
  have compositeUnary : UnaryHistory composite :=
    unary_cont_closed surface.right.left identityUnary surface.right.right.right
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro identityUnary
        (And.intro compositeUnary
          (And.intro surface.right.right.left surface.right.right.right))))

theorem PreSheafIndexedRestrictionSurface_ledger_extension_surface
    {sec rho identity composite transport ledger : BHist} :
    PreSheafIndexedRestrictionSurface sec rho identity composite ->
      Cont identity composite transport -> Cont composite transport ledger ->
        PreSheafIndexedRestrictionSurface identity composite transport ledger ∧
          UnaryHistory transport ∧ UnaryHistory ledger := by
  intro surface transportCont ledgerCont
  have rows := PreSheafIndexedRestrictionSurface_carrier_rows surface
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed rows.right.right.left rows.right.right.right.left transportCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed rows.right.right.right.left transportUnary ledgerCont
  exact And.intro
    (And.intro rows.right.right.left
      (And.intro rows.right.right.right.left
        (And.intro transportCont ledgerCont)))
    (And.intro transportUnary ledgerUnary)

end BEDC.Derived.PreSheafUp
