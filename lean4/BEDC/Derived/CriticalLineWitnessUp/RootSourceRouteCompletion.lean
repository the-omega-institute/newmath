import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_route_completion
    {Z S M R Q H C P N sourceRead rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead Q rootRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory sourceRead ∧ UnaryHistory rootRead ∧
              hsame H (append Z S) ∧ Cont Z S sourceRead ∧
                Cont sourceRead Q rootRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceRoute rootRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have unaryRootRead : UnaryHistory rootRead :=
    unary_cont_closed unarySourceRead unaryQ rootRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unarySourceRead, unaryRootRead,
      sameH, sourceRoute, rootRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
