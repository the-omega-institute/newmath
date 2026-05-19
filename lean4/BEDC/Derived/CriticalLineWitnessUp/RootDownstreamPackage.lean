import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_downstream_package
    {Z S M R Q H C P N rootRead downstream : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q rootRead ->
        Cont rootRead N downstream ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
            UnaryHistory rootRead ∧ UnaryHistory downstream ∧ hsame H (append Z S) ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                Cont (append Z S) Q rootRead ∧ Cont rootRead N downstream := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet rootRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary unaryQ rootRoute
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed rootUnary unaryN downstreamRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, unaryN, rootUnary, downstreamUnary, sameH, routeQ, routeC,
      routeN, rootRoute, downstreamRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
