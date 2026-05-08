import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BilinFormBHistObligationSurface
    (left right scalar additive endpoint scalarLedger ledger : BHist) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory scalar ∧ UnaryHistory additive ∧
    Cont left right endpoint ∧ Cont endpoint scalar scalarLedger ∧
      Cont scalarLedger additive ledger

theorem BilinFormBHistObligationSurface_carrier_classifier_obligations
    {left right scalar additive endpoint scalarLedger ledger endpoint' scalarLedger' ledger' : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      hsame endpoint endpoint' ->
        Cont left right endpoint' ->
          Cont endpoint' scalar scalarLedger' ->
            Cont scalarLedger' additive ledger' ->
              BilinFormBHistObligationSurface left right scalar additive endpoint' scalarLedger' ledger' ∧
                UnaryHistory endpoint' ∧ UnaryHistory scalarLedger' ∧ UnaryHistory ledger' ∧
                  hsame endpoint endpoint' ∧ hsame scalarLedger scalarLedger' ∧
                    hsame ledger ledger' := by
  intro surface sameEndpoint endpointCont scalarLedgerCont ledgerCont
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed surface.left surface.right.left endpointCont
  have scalarLedgerUnary : UnaryHistory scalarLedger' :=
    unary_cont_closed endpointUnary surface.right.right.left scalarLedgerCont
  have ledgerUnary : UnaryHistory ledger' :=
    unary_cont_closed scalarLedgerUnary surface.right.right.right.left ledgerCont
  have sameScalarLedger : hsame scalarLedger scalarLedger' :=
    cont_respects_hsame sameEndpoint (hsame_refl scalar)
      surface.right.right.right.right.right.left scalarLedgerCont
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameScalarLedger (hsame_refl additive)
      surface.right.right.right.right.right.right ledgerCont
  constructor
  · exact
      And.intro surface.left
        (And.intro surface.right.left
          (And.intro surface.right.right.left
            (And.intro surface.right.right.right.left
              (And.intro endpointCont
                (And.intro scalarLedgerCont ledgerCont)))))
  · exact
      And.intro endpointUnary
        (And.intro scalarLedgerUnary
          (And.intro ledgerUnary
            (And.intro sameEndpoint
              (And.intro sameScalarLedger sameLedger))))

theorem BilinFormBHistObligationSurface_symmetry_antisymmetry_obligations
    {left right scalar additive endpoint scalarLedger ledger swappedEndpoint swappedScalarLedger
      swappedLedger : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      Cont right left swappedEndpoint ->
        Cont swappedEndpoint scalar swappedScalarLedger ->
          Cont swappedScalarLedger additive swappedLedger ->
            BilinFormBHistObligationSurface right left scalar additive swappedEndpoint
                swappedScalarLedger swappedLedger ∧
              hsame endpoint swappedEndpoint ∧ hsame scalarLedger swappedScalarLedger ∧
                hsame ledger swappedLedger := by
  intro surface swappedEndpointCont swappedScalarLedgerCont swappedLedgerCont
  have sameEndpoint : hsame endpoint swappedEndpoint :=
    unary_cont_comm surface.left surface.right.left surface.right.right.right.right.left
      swappedEndpointCont
  have sameScalarLedger : hsame scalarLedger swappedScalarLedger :=
    cont_respects_hsame sameEndpoint (hsame_refl scalar)
      surface.right.right.right.right.right.left swappedScalarLedgerCont
  have sameLedger : hsame ledger swappedLedger :=
    cont_respects_hsame sameScalarLedger (hsame_refl additive)
      surface.right.right.right.right.right.right swappedLedgerCont
  constructor
  · exact
      And.intro surface.right.left
        (And.intro surface.left
          (And.intro surface.right.right.left
            (And.intro surface.right.right.right.left
              (And.intro swappedEndpointCont
                (And.intro swappedScalarLedgerCont swappedLedgerCont)))))
  · exact And.intro sameEndpoint
      (And.intro sameScalarLedger sameLedger)

def BilinFormRootPairingSurface
    (left right scalar endpoint ledger : BHist) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory scalar ∧
    Cont left right endpoint ∧ Cont endpoint scalar ledger

theorem BilinFormRootPairingSurface_ledger_exactness_boundary
    {left right scalar endpoint ledger : BHist} :
    BilinFormRootPairingSurface left right scalar endpoint ledger ->
      UnaryHistory endpoint ∧ UnaryHistory ledger ∧ hsame endpoint (append left right) ∧
        hsame ledger (append (append left right) scalar) ∧ Cont left right endpoint ∧
          Cont endpoint scalar ledger := by
  intro surface
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed surface.left surface.right.left surface.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpointUnary surface.right.right.left surface.right.right.right.right
  have ledgerReadback : hsame ledger (append (append left right) scalar) :=
    hsame_trans surface.right.right.right.right
      (congrArg (fun h : BHist => append h scalar) surface.right.right.right.left)
  exact And.intro endpointUnary
    (And.intro ledgerUnary
      (And.intro surface.right.right.right.left
        (And.intro ledgerReadback
          (And.intro surface.right.right.right.left surface.right.right.right.right))))

theorem BilinFormRootPairingSurface_symmetry_rows
    {left right scalar endpoint ledger swappedEndpoint swappedLedger : BHist} :
    BilinFormRootPairingSurface left right scalar endpoint ledger ->
      Cont right left swappedEndpoint ->
        Cont swappedEndpoint scalar swappedLedger ->
          BilinFormRootPairingSurface right left scalar swappedEndpoint swappedLedger ∧
            hsame endpoint swappedEndpoint ∧ hsame ledger swappedLedger := by
  intro surface swappedEndpointCont swappedLedgerCont
  have sameEndpoint : hsame endpoint swappedEndpoint :=
    unary_cont_comm surface.left surface.right.left surface.right.right.right.left
      swappedEndpointCont
  have sameLedger : hsame ledger swappedLedger :=
    cont_respects_hsame sameEndpoint (hsame_refl scalar)
      surface.right.right.right.right swappedLedgerCont
  constructor
  · exact
      And.intro surface.right.left
        (And.intro surface.left
          (And.intro surface.right.right.left
            (And.intro swappedEndpointCont swappedLedgerCont)))
  · exact And.intro sameEndpoint sameLedger

theorem BilinFormRootPairingSurface_bilinearity_rows
    {left right scalar endpoint ledger additive additiveEndpoint finalLedger : BHist} :
    BilinFormRootPairingSurface left right scalar endpoint ledger ->
      UnaryHistory additive ->
        Cont endpoint additive additiveEndpoint ->
          Cont additiveEndpoint scalar finalLedger ->
            UnaryHistory additiveEndpoint ∧ UnaryHistory finalLedger ∧
              hsame additiveEndpoint (append (append left right) additive) ∧
                hsame finalLedger (append (append (append left right) additive) scalar) ∧
                  Cont endpoint additive additiveEndpoint ∧
                    Cont additiveEndpoint scalar finalLedger := by
  intro surface additiveUnary additiveCont finalCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed surface.left surface.right.left surface.right.right.right.left
  have additiveEndpointUnary : UnaryHistory additiveEndpoint :=
    unary_cont_closed endpointUnary additiveUnary additiveCont
  have finalLedgerUnary : UnaryHistory finalLedger :=
    unary_cont_closed additiveEndpointUnary surface.right.right.left finalCont
  have additiveReadback :
      hsame additiveEndpoint (append (append left right) additive) :=
    hsame_trans additiveCont
      (congrArg (fun h : BHist => append h additive) surface.right.right.right.left)
  have finalReadback :
      hsame finalLedger (append (append (append left right) additive) scalar) :=
    hsame_trans finalCont
      (congrArg (fun h : BHist => append h scalar) additiveReadback)
  exact And.intro additiveEndpointUnary
    (And.intro finalLedgerUnary
      (And.intro additiveReadback
        (And.intro finalReadback
          (And.intro additiveCont finalCont))))

theorem BilinFormRootPairingSurface_input_transport
    {left left' right right' scalar scalar' endpoint endpoint' ledger ledger' : BHist} :
    BilinFormRootPairingSurface left right scalar endpoint ledger ->
      hsame left left' ->
        hsame right right' ->
          hsame scalar scalar' ->
            Cont left' right' endpoint' ->
              Cont endpoint' scalar' ledger' ->
                BilinFormRootPairingSurface left' right' scalar' endpoint' ledger' ∧
                  hsame endpoint endpoint' ∧ hsame ledger ledger' := by
  intro surface sameLeft sameRight sameScalar endpointCont ledgerCont
  have leftUnary : UnaryHistory left' :=
    unary_transport surface.left sameLeft
  have rightUnary : UnaryHistory right' :=
    unary_transport surface.right.left sameRight
  have scalarUnary : UnaryHistory scalar' :=
    unary_transport surface.right.right.left sameScalar
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLeft sameRight surface.right.right.right.left endpointCont
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameEndpoint sameScalar surface.right.right.right.right ledgerCont
  constructor
  · exact
      And.intro leftUnary
        (And.intro rightUnary
            (And.intro scalarUnary
              (And.intro endpointCont ledgerCont)))
  · exact And.intro sameEndpoint sameLedger

def BilinFormModulePairingSourceRow
    (moduleSource vecSource left right scalar endpoint probes ledger : BHist)
    (bundle : ProbeBundle BHist) : Prop :=
  UnaryHistory moduleSource ∧ UnaryHistory vecSource ∧
    BilinFormRootPairingSurface left right scalar endpoint ledger ∧ InBundle probes bundle

theorem BilinFormModulePairingSourceRow_pairing_classifier_row
    {moduleSource vecSource left right scalar endpoint probes ledger endpoint' ledger' : BHist}
    {bundle : ProbeBundle BHist} :
    BilinFormModulePairingSourceRow moduleSource vecSource left right scalar endpoint probes ledger
        bundle ->
      hsame endpoint endpoint' ->
        Cont left right endpoint' ->
          Cont endpoint' scalar ledger' ->
            BilinFormRootPairingSurface left right scalar endpoint' ledger' ∧
              hsame ledger ledger' ∧ InBundle probes bundle := by
  intro row sameEndpoint endpointCont ledgerCont
  have transported :=
    BilinFormRootPairingSurface_input_transport row.right.right.left (hsame_refl left)
      (hsame_refl right) (hsame_refl scalar) endpointCont ledgerCont
  exact And.intro transported.left (And.intro transported.right.right row.right.right.right)

end BEDC.Derived.BilinFormUp
