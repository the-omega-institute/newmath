import BEDC.Derived.DiffFormUp
import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ContactUp

open BEDC.Derived.DiffFormUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ContactCarrierDiffFormLedgerSurface
    (manifold form derivative degree degreePlus probe probe' tensor tensor' scalar scalar'
      antisym source wedge top hyperplane ledger : BHist) : Prop :=
  ManifoldSingletonCarrier manifold ∧
    DiffFormExteriorDerivativeLedger form derivative degree degreePlus probe probe' tensor
      tensor' scalar scalar' antisym source ∧
      DiffFormWedgeDegreeLedger degree degreePlus wedge form derivative tensor ∧
        Cont wedge hyperplane top ∧ hsame ledger top

theorem ContactUpLedgerExactness_obligation
    {manifold form derivative degree degreePlus probe probe' tensor tensor' scalar scalar'
      antisym source wedge top hyperplane ledger transportedTop : BHist} :
    ContactCarrierDiffFormLedgerSurface manifold form derivative degree degreePlus probe probe'
        tensor tensor' scalar scalar' antisym source wedge top hyperplane ledger ->
      hsame top transportedTop ->
        ContactCarrierDiffFormLedgerSurface manifold form derivative degree degreePlus probe probe'
            tensor tensor' scalar scalar' antisym source wedge transportedTop hyperplane
            transportedTop ∧
          hsame ledger transportedTop ∧ UnaryHistory wedge := by
  intro surface sameTop
  have transportedCont : Cont wedge hyperplane transportedTop :=
    cont_result_hsame_transport surface.right.right.right.left sameTop
  have transportedSurface :
      ContactCarrierDiffFormLedgerSurface manifold form derivative degree degreePlus probe probe'
        tensor tensor' scalar scalar' antisym source wedge transportedTop hyperplane
        transportedTop :=
    And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro transportedCont (hsame_refl transportedTop))))
  have sameLedger : hsame ledger transportedTop :=
    hsame_trans surface.right.right.right.right sameTop
  have wedgeUnary : UnaryHistory wedge :=
    surface.right.right.left.right.right.right.left
  exact And.intro transportedSurface
    (And.intro sameLedger wedgeUnary)

def ContactCarrierClassifierSurface (manifold form derivative wedge top : BHist) : Prop :=
  ManifoldSingletonCarrier manifold ∧ UnaryHistory form ∧ UnaryHistory derivative ∧
    Cont form derivative wedge ∧ Cont wedge BHist.Empty top

theorem ContactCarrierClassifierSurface_form_row_obligation
    {manifold form derivative wedge top : BHist} :
    ContactCarrierClassifierSurface manifold form derivative wedge top ->
      ManifoldSingletonCarrier manifold ∧ UnaryHistory manifold ∧ UnaryHistory form ∧
        UnaryHistory derivative ∧ UnaryHistory wedge ∧ UnaryHistory top ∧
          Cont form derivative wedge ∧ Cont wedge BHist.Empty top := by
  intro surface
  have manifoldRows := ManifoldSingletonCarrier_topology_scope surface.left
  have wedgeUnary : UnaryHistory wedge :=
    unary_cont_closed surface.right.left surface.right.right.left surface.right.right.right.left
  have topUnary : UnaryHistory top :=
    unary_cont_closed wedgeUnary unary_empty surface.right.right.right.right
  exact And.intro surface.left
    (And.intro manifoldRows.right.left
      (And.intro surface.right.left
          (And.intro surface.right.right.left
            (And.intro wedgeUnary
              (And.intro topUnary
                (And.intro surface.right.right.right.left surface.right.right.right.right))))))

theorem ContactCarrierClassifierSurface_nondegeneracy_obligation
    {manifold form derivative wedge top tail : BHist} :
    ContactCarrierClassifierSurface manifold form derivative wedge top ->
      hsame wedge (BHist.e1 tail) ->
        UnaryHistory top ∧ hsame top wedge ∧ (hsame top BHist.Empty -> False) := by
  intro surface sameWedgeVisible
  have topSameWedge : hsame top wedge :=
    cont_right_unit_result surface.right.right.right.right
  have topNonempty : hsame top BHist.Empty -> False := by
    intro topEmpty
    have wedgeEmpty : hsame wedge BHist.Empty :=
      hsame_trans (hsame_symm topSameWedge) topEmpty
    have visibleEmpty : hsame (BHist.e1 tail) BHist.Empty :=
      hsame_trans (hsame_symm sameWedgeVisible) wedgeEmpty
    exact not_hsame_e1_empty visibleEmpty
  have wedgeUnary : UnaryHistory wedge :=
    unary_cont_closed surface.right.left surface.right.right.left surface.right.right.right.left
  have topUnary : UnaryHistory top :=
    unary_cont_closed wedgeUnary unary_empty surface.right.right.right.right
  exact And.intro
    topUnary
    (And.intro topSameWedge topNonempty)

theorem ContactCarrierClassifierSurface_top_wedge_transport_with_wedge
    {manifold form derivative wedge top top' : BHist} :
    ContactCarrierClassifierSurface manifold form derivative wedge top ->
      hsame top top' ->
        ContactCarrierClassifierSurface manifold form derivative wedge top' ∧
          UnaryHistory top' ∧ hsame top' wedge := by
  intro surface sameTop
  have rows :=
    ContactCarrierClassifierSurface_form_row_obligation surface
  have topRow : Cont wedge BHist.Empty top' :=
    cont_result_hsame_transport rows.right.right.right.right.right.right.right sameTop
  have topUnary : UnaryHistory top' :=
    unary_transport rows.right.right.right.right.right.left sameTop
  have topWedge : hsame top' wedge :=
    hsame_trans (hsame_symm sameTop)
      (cont_right_unit_result rows.right.right.right.right.right.right.right)
  exact And.intro
    (And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro surface.right.right.right.left topRow))))
    (And.intro topUnary topWedge)

theorem ContactCarrierClassifierSurface_public_namecert_export
    {manifold form derivative wedge top top' tail : BHist} :
    ContactCarrierClassifierSurface manifold form derivative wedge top ->
      hsame top top' ->
        hsame wedge (BHist.e1 tail) ->
          ContactCarrierClassifierSurface manifold form derivative wedge top' ∧
            UnaryHistory form ∧ UnaryHistory derivative ∧ UnaryHistory wedge ∧
              UnaryHistory top' ∧ hsame top' wedge ∧
                (hsame top' BHist.Empty -> False) := by
  intro surface sameTop sameWedgeVisible
  have transported :=
    ContactCarrierClassifierSurface_top_wedge_transport_with_wedge surface sameTop
  have rows :=
    ContactCarrierClassifierSurface_form_row_obligation transported.left
  have topNonempty : hsame top' BHist.Empty -> False := by
    intro topEmpty
    have wedgeEmpty : hsame wedge BHist.Empty :=
      hsame_trans (hsame_symm transported.right.right) topEmpty
    have visibleEmpty : hsame (BHist.e1 tail) BHist.Empty :=
      hsame_trans (hsame_symm sameWedgeVisible) wedgeEmpty
    exact not_hsame_e1_empty visibleEmpty
  exact And.intro transported.left
    (And.intro rows.right.right.left
      (And.intro rows.right.right.right.left
        (And.intro rows.right.right.right.right.left
          (And.intro transported.right.left
            (And.intro transported.right.right topNonempty)))))

def ContactStandardBridgeSurface
    (manifold form derivative wedge top top' bridge ledger : BHist) : Prop :=
  ContactCarrierClassifierSurface manifold form derivative wedge top ∧ hsame top top' ∧
    Cont top' bridge ledger ∧ hsame bridge BHist.Empty

theorem ContactStandardBridgeSurface_public_bridge_compatibility
    {manifold form derivative wedge top top' tail : BHist} :
    ContactCarrierClassifierSurface manifold form derivative wedge top ->
      hsame top top' ->
        hsame wedge (BHist.e1 tail) ->
          ContactCarrierClassifierSurface manifold form derivative wedge top' ∧
            Cont wedge BHist.Empty top' ∧ UnaryHistory top' ∧ hsame top' wedge ∧
              (hsame top' BHist.Empty -> False) := by
  intro surface sameTop sameWedgeVisible
  have transported :=
    ContactCarrierClassifierSurface_top_wedge_transport_with_wedge surface sameTop
  have exported :=
    ContactCarrierClassifierSurface_public_namecert_export surface sameTop sameWedgeVisible
  exact And.intro transported.left
    (And.intro transported.left.right.right.right.right
      (And.intro transported.right.left
        (And.intro transported.right.right exported.right.right.right.right.right.right)))

theorem ContactCarrierClassifierSurface_top_wedge_transport
    {manifold form derivative wedge top top' : BHist} :
    ContactCarrierClassifierSurface manifold form derivative wedge top ->
      hsame top top' ->
        ContactCarrierClassifierSurface manifold form derivative wedge top' ∧
          UnaryHistory top' := by
  intro surface sameTop
  have topRow' : Cont wedge BHist.Empty top' :=
    cont_result_hsame_transport surface.right.right.right.right sameTop
  have transportedSurface :
      ContactCarrierClassifierSurface manifold form derivative wedge top' :=
    And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro surface.right.right.right.left topRow')))
  have transportedRows :=
    ContactCarrierClassifierSurface_form_row_obligation transportedSurface
  exact And.intro transportedSurface transportedRows.right.right.right.right.right.left

theorem ContactCarrierClassifierSurface_public_bridge_compatibility
    {manifold form derivative wedge top bridge top' tail : BHist} :
    ContactCarrierClassifierSurface manifold form derivative wedge top ->
      hsame top bridge ->
        hsame bridge top' ->
          hsame wedge (BHist.e1 tail) ->
            ContactCarrierClassifierSurface manifold form derivative wedge top' ∧
              hsame top' wedge ∧ UnaryHistory top' ∧ (hsame top' BHist.Empty -> False) := by
  intro surface sameTopBridge sameBridgeTop sameWedgeVisible
  have sameTopTop' : hsame top top' :=
    hsame_trans sameTopBridge sameBridgeTop
  have exported :=
    ContactCarrierClassifierSurface_public_namecert_export surface sameTopTop' sameWedgeVisible
  exact And.intro exported.left
    (And.intro exported.right.right.right.right.right.left
      (And.intro exported.right.right.right.right.left
        exported.right.right.right.right.right.right))

end BEDC.Derived.ContactUp
