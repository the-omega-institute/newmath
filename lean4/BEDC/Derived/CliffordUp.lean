import BEDC.FKernel.Unary

namespace BEDC.Derived.CliffordUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def CliffordCarrierPackage (word quadratic product : BHist) : Prop :=
  UnaryHistory word ∧ UnaryHistory quadratic ∧ Cont word quadratic product

theorem CliffordCarrierPackage_product_relation_stability_obligations
    {left right context leftProduct rightProduct quadratic : BHist} :
    CliffordCarrierPackage left quadratic (append left quadratic) ->
      CliffordCarrierPackage right quadratic (append right quadratic) ->
        hsame left right ->
          UnaryHistory context ->
            Cont left context leftProduct ->
              Cont right context rightProduct ->
                CliffordCarrierPackage leftProduct quadratic (append leftProduct quadratic) ∧
                  CliffordCarrierPackage rightProduct quadratic (append rightProduct quadratic) ∧
                    hsame leftProduct rightProduct := by
  intro leftPackage rightPackage sameLeftRight contextCarrier leftContext rightContext
  have leftProductCarrier : UnaryHistory leftProduct :=
    unary_cont_closed leftPackage.left contextCarrier leftContext
  have rightProductCarrier : UnaryHistory rightProduct :=
    unary_cont_closed rightPackage.left contextCarrier rightContext
  have sameProducts : hsame leftProduct rightProduct :=
    cont_respects_hsame sameLeftRight (hsame_refl context) leftContext rightContext
  constructor
  · exact And.intro leftProductCarrier (And.intro leftPackage.right.left (cont_intro rfl))
  · constructor
    · exact And.intro rightProductCarrier (And.intro rightPackage.right.left (cont_intro rfl))
    · exact sameProducts

end BEDC.Derived.CliffordUp
