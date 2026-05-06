import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LieGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def LieGroupSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def LieGroupSingletonMul (h k : BHist) : BHist :=
  append h k

def LieGroupSingletonInv (_h : BHist) : BHist :=
  BHist.Empty

theorem LieGroupSingleton_operation_smoothness {h k mulChart invChart : BHist} :
    LieGroupSingletonCarrier h -> LieGroupSingletonCarrier k ->
      Cont BHist.Empty (LieGroupSingletonMul h k) mulChart ->
        Cont BHist.Empty (LieGroupSingletonInv h) invChart ->
          hsame mulChart BHist.Empty ∧ hsame invChart BHist.Empty ∧
            UnaryHistory mulChart ∧ UnaryHistory invChart := by
  intro carrierH carrierK mulChartRow invChartRow
  have mulEndpointEmpty : hsame (LieGroupSingletonMul h k) BHist.Empty := by
    exact append_eq_empty_iff.mpr (And.intro carrierH carrierK)
  have mulChartEndpoint : hsame mulChart (LieGroupSingletonMul h k) :=
    cont_left_unit_result mulChartRow
  have mulChartEmpty : hsame mulChart BHist.Empty :=
    hsame_trans mulChartEndpoint mulEndpointEmpty
  have invChartEndpoint : hsame invChart (LieGroupSingletonInv h) :=
    cont_left_unit_result invChartRow
  have invChartEmpty : hsame invChart BHist.Empty :=
    invChartEndpoint
  have mulChartUnary : UnaryHistory mulChart :=
    unary_transport unary_empty (hsame_symm mulChartEmpty)
  have invChartUnary : UnaryHistory invChart :=
    unary_transport unary_empty (hsame_symm invChartEmpty)
  exact And.intro mulChartEmpty
    (And.intro invChartEmpty (And.intro mulChartUnary invChartUnary))

end BEDC.Derived.LieGroupUp
