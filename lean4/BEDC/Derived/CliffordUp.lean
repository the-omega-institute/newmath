import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CliffordUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CliffordCarrierPackage_product_stability_obligation
    {left left' right right' product product' : BHist} :
    UnaryHistory left -> UnaryHistory right ->
      hsame left left' -> hsame right right' ->
        Cont left right product -> Cont left' right' product' ->
          UnaryHistory product ∧ UnaryHistory product' ∧ hsame product product' := by
  intro leftCarrier rightCarrier sameLeft sameRight productCont productCont'
  have productCarrier : UnaryHistory product :=
    unary_cont_closed leftCarrier rightCarrier productCont
  have leftCarrier' : UnaryHistory left' :=
    unary_transport leftCarrier sameLeft
  have rightCarrier' : UnaryHistory right' :=
    unary_transport rightCarrier sameRight
  have productCarrier' : UnaryHistory product' :=
    unary_cont_closed leftCarrier' rightCarrier' productCont'
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameLeft sameRight productCont productCont'
  exact And.intro productCarrier (And.intro productCarrier' sameProduct)

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
