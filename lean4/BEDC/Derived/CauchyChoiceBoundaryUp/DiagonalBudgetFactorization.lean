import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyChoiceBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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

end BEDC.Derived.CauchyChoiceBoundaryUp
