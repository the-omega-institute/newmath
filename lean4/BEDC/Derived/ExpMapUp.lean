import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.LieGroupUp

namespace BEDC.Derived.ExpMapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.LieAlgebraUp
open BEDC.Derived.LieGroupUp

theorem ExpMapZeroFlow_obligation_surface {zero flowA flowB mid out direct : BHist} :
    LieAlgebraSingletonCarrier zero -> LieAlgebraSingletonCarrier flowA ->
      LieAlgebraSingletonCarrier flowB -> Cont zero flowA mid -> Cont mid flowB out ->
        Cont flowA flowB direct ->
          hsame mid flowA ∧ hsame out direct ∧ LieGroupSingletonCarrier out ∧
            UnaryHistory out ∧ UnaryHistory direct := by
  intro zeroCarrier flowACarrier flowBCarrier zeroFlow flowStep directStep
  have sameMidFlowA : hsame mid flowA :=
    cont_respects_hsame zeroCarrier (hsame_refl flowA) zeroFlow (cont_left_unit flowA)
  have sameOutDirect : hsame out direct :=
    cont_respects_hsame sameMidFlowA (hsame_refl flowB) flowStep directStep
  have directCarrier : hsame direct BHist.Empty :=
    cont_respects_hsame flowACarrier flowBCarrier directStep (cont_left_unit BHist.Empty)
  have outCarrier : LieGroupSingletonCarrier out :=
    hsame_trans sameOutDirect directCarrier
  have outUnary : UnaryHistory out :=
    unary_transport unary_empty (hsame_symm outCarrier)
  have directUnary : UnaryHistory direct :=
    unary_transport unary_empty (hsame_symm directCarrier)
  exact And.intro sameMidFlowA
    (And.intro sameOutDirect (And.intro outCarrier (And.intro outUnary directUnary)))

end BEDC.Derived.ExpMapUp
