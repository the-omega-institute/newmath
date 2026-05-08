import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CliffordUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CliffordCarrierPackage (unit vector product boundary endpoint : BHist) : Prop :=
  UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory boundary ∧
    Cont vector vector product ∧ Cont product boundary endpoint

theorem CliffordCarrierPackage_product_relation_stability
    {unit vector vector' product product' boundary endpoint endpoint' : BHist} :
    CliffordCarrierPackage unit vector product boundary endpoint ->
      hsame vector vector' ->
        Cont vector' vector' product' ->
          Cont product' boundary endpoint' ->
            CliffordCarrierPackage unit vector' product' boundary endpoint' ∧
              hsame product product' ∧ hsame endpoint endpoint' := by
  intro carrier sameVector productCont endpointCont
  have vector'Unary : UnaryHistory vector' :=
    unary_transport carrier.right.left sameVector
  have productUnary : UnaryHistory product' :=
    unary_cont_closed vector'Unary vector'Unary productCont
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameVector sameVector carrier.right.right.right.left productCont
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProduct (hsame_refl boundary)
      carrier.right.right.right.right endpointCont
  constructor
  · exact
      And.intro carrier.left
        (And.intro vector'Unary
          (And.intro carrier.right.right.left
            (And.intro productCont endpointCont)))
  · exact And.intro sameProduct sameEndpoint

end BEDC.Derived.CliffordUp
