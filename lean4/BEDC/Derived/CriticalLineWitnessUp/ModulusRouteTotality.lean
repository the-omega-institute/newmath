import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_route_totality
    {Z S M R Q H C P N depthRead modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R depthRead ->
        Cont depthRead H modulusRead ->
          Cont N Q refusalRead ->
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory depthRead ∧
              UnaryHistory modulusRead ∧ UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
                Cont M R Q ∧ Cont M R depthRead ∧ Cont depthRead H modulusRead ∧
                  Cont N Q refusalRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet depthRoute modulusRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC _unaryP routeN
  have unaryDepthRead : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryDepthRead unaryH modulusRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  exact
    ⟨unaryM, unaryR, unaryQ, unaryDepthRead, unaryModulusRead, unaryRefusalRead,
      sameH, routeQ, depthRoute, modulusRoute, refusalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
