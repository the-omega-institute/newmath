import BEDC.Derived.DiffFormUp
import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ContactUp

open BEDC.Derived.DiffFormUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ContactCarrierClassifierSurface
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
    ContactCarrierClassifierSurface manifold form derivative degree degreePlus probe probe'
        tensor tensor' scalar scalar' antisym source wedge top hyperplane ledger ->
      hsame top transportedTop ->
        ContactCarrierClassifierSurface manifold form derivative degree degreePlus probe probe'
            tensor tensor' scalar scalar' antisym source wedge transportedTop hyperplane
            transportedTop ∧
          hsame ledger transportedTop ∧ UnaryHistory wedge := by
  intro surface sameTop
  have transportedCont : Cont wedge hyperplane transportedTop :=
    cont_result_hsame_transport surface.right.right.right.left sameTop
  have transportedSurface :
      ContactCarrierClassifierSurface manifold form derivative degree degreePlus probe probe'
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

end BEDC.Derived.ContactUp
