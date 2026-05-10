import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Unary

namespace BEDC.Derived.PreSheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem PreSheafIndexedRestrictionSurface_restriction_composition_row
    {sec rho identity composite secRho rhoIdentity direct nested : BHist} :
    PreSheafIndexedRestrictionSurface sec rho identity composite ->
      Cont sec rho secRho -> Cont secRho identity direct ->
        Cont rho identity rhoIdentity -> Cont sec rhoIdentity nested ->
          hsame direct nested ∧ hsame secRho identity ∧ hsame rhoIdentity composite := by
  intro surface secRhoRow directRow rhoIdentityRow nestedRow
  have directNested : hsame direct nested :=
    cont_assoc_hsame secRhoRow directRow rhoIdentityRow nestedRow
  have secRhoIdentity : hsame secRho identity :=
    cont_deterministic secRhoRow surface.right.right.left
  have rhoIdentityComposite : hsame rhoIdentity composite :=
    cont_deterministic rhoIdentityRow surface.right.right.right
  exact And.intro directNested (And.intro secRhoIdentity rhoIdentityComposite)

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

theorem PreSheafIndexedRestrictionSurface_empty_restriction_identity_row
    {sec identity composite : BHist} :
    PreSheafIndexedRestrictionSurface sec BHist.Empty identity composite ->
      hsame identity sec ∧ hsame composite identity ∧ UnaryHistory identity ∧
        UnaryHistory composite ∧ Cont BHist.Empty identity composite := by
  intro surface
  have sameIdentity : hsame identity sec :=
    cont_right_unit_result surface.right.right.left
  have sameComposite : hsame composite identity :=
    cont_left_unit_result surface.right.right.right
  have identityUnary : UnaryHistory identity :=
    unary_transport surface.left (hsame_symm sameIdentity)
  have compositeUnary : UnaryHistory composite :=
    unary_transport identityUnary (hsame_symm sameComposite)
  exact And.intro sameIdentity
    (And.intro sameComposite
      (And.intro identityUnary
        (And.intro compositeUnary surface.right.right.right)))

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

theorem PreSheafIndexedRestrictionSurface_StdBridge {sec rho identity composite : BHist} :
    PreSheafIndexedRestrictionSurface sec rho identity composite ->
      SemanticNameCert
        (fun h : BHist => PreSheafIndexedRestrictionSurface sec rho identity h)
        (fun h : BHist => PreSheafIndexedRestrictionSurface sec rho identity h)
        (fun h : BHist => PreSheafIndexedRestrictionSurface sec rho identity h)
        hsame := by
  intro surface
  constructor
  · constructor
    · exact Exists.intro composite surface
    · intro h _source
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same source
      exact And.intro source.left
        (And.intro source.right.left
          (And.intro source.right.right.left
            (cont_result_hsame_transport source.right.right.right same)))
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.PreSheafUp
