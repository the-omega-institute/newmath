import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_downstream_modulus_comparison_totality
    {Z S M R Q H C P N zeroRead modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont M R modulusRead ->
          Cont modulusRead Q refusalRead ->
            UnaryHistory zeroRead ∧ UnaryHistory modulusRead ∧
              UnaryHistory refusalRead ∧ hsame H (append Z S) ∧ Cont Z S zeroRead ∧
                Cont M R modulusRead ∧ Cont modulusRead Q refusalRead ∧ Cont Q H C ∧
                  Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zeroRoute modulusRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, _routeQ, routeC, routeN⟩ :=
    packet
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR _routeQ
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed modulusReadUnary unaryQ refusalRoute
  exact
    ⟨zeroReadUnary, modulusReadUnary, refusalReadUnary, sameH, zeroRoute, modulusRoute,
      refusalRoute, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_downstream_refusal_export
    {Z S M R Q H C P N zeroRead modulusRead refusalRead exportRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont M R modulusRead ->
          Cont modulusRead Q refusalRead ->
            Cont refusalRead C exportRead ->
              UnaryHistory zeroRead ∧ UnaryHistory modulusRead ∧
                UnaryHistory refusalRead ∧ UnaryHistory exportRead ∧ hsame H (append Z S) ∧
                  Cont Z S zeroRead ∧ Cont M R modulusRead ∧
                    Cont modulusRead Q refusalRead ∧ Cont refusalRead C exportRead ∧
                      Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zeroRoute modulusRoute refusalRoute exportRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed modulusReadUnary unaryQ refusalRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed refusalReadUnary unaryC exportRoute
  exact
    ⟨zeroReadUnary, modulusReadUnary, refusalReadUnary, exportReadUnary, sameH, zeroRoute,
      modulusRoute, refusalRoute, exportRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
