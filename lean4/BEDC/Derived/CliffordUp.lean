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

end BEDC.Derived.CliffordUp
