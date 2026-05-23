import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyChoiceBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CauchyChoiceBoundaryCarrier (M E I T S R H C P N : BHist) : Prop :=
  UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory I ∧ UnaryHistory T ∧ UnaryHistory S ∧
    UnaryHistory R ∧ hsame H (append M E) ∧ Cont C P N

theorem CauchyChoiceBoundaryDiagonalBudgetFactorization
    {M E I T S R _H _C _P _N selectedRead tailRead sealRead : BHist} :
    Cont M E I ->
      Cont I T selectedRead ->
        Cont selectedRead S tailRead ->
          Cont tailRead R sealRead ->
            UnaryHistory M ->
              UnaryHistory E ->
                UnaryHistory I ->
                  UnaryHistory T ->
                    UnaryHistory S ->
                      UnaryHistory R ->
                        UnaryHistory selectedRead ∧ UnaryHistory tailRead ∧
                          UnaryHistory sealRead ∧ Cont M E I ∧
                            Cont I T selectedRead ∧ Cont selectedRead S tailRead ∧
                              Cont tailRead R sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro routeI routeSelected routeTail routeSeal unaryM unaryE _unaryI unaryT unaryS
    unaryR
  have derivedUnaryI : UnaryHistory I :=
    unary_cont_closed unaryM unaryE routeI
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed derivedUnaryI unaryT routeSelected
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed selectedUnary unaryS routeTail
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary unaryR routeSeal
  exact
    ⟨selectedUnary, tailUnary, sealUnary, routeI, routeSelected, routeTail, routeSeal⟩

theorem CauchyChoiceBoundaryScopedConsumerRoute
    {M E I T S R H C P N budgetRead selectedRead tailRead sealRead scopedRead : BHist} :
    CauchyChoiceBoundaryCarrier M E I T S R H C P N ->
      Cont M E budgetRead ->
        Cont budgetRead I selectedRead ->
          Cont selectedRead T tailRead ->
            Cont tailRead S sealRead ->
              Cont sealRead R scopedRead ->
                UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory I ∧ UnaryHistory T ∧
                  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory budgetRead ∧
                    UnaryHistory selectedRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory scopedRead ∧
                        hsame H (append M E) ∧ Cont M E budgetRead ∧
                          Cont budgetRead I selectedRead ∧ Cont selectedRead T tailRead ∧
                            Cont tailRead S sealRead ∧ Cont sealRead R scopedRead ∧
                              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet budgetRoute selectedRoute tailRoute sealRoute scopedRoute
  obtain ⟨unaryM, unaryE, unaryI, unaryT, unaryS, unaryR, sameH, routeN⟩ := packet
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed unaryM unaryE budgetRoute
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed budgetUnary unaryI selectedRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed selectedUnary unaryT tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary unaryS sealRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed sealUnary unaryR scopedRoute
  exact
    ⟨unaryM, unaryE, unaryI, unaryT, unaryS, unaryR, budgetUnary, selectedUnary,
      tailUnary, sealUnary, scopedUnary, sameH, budgetRoute, selectedRoute, tailRoute,
      sealRoute, scopedRoute, routeN⟩

end BEDC.Derived.CauchyChoiceBoundaryUp
