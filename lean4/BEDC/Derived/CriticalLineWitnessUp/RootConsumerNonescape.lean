import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_consumer_nonescape
    {Z S M R Q H C P N visibleRead refusalRead rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q visibleRead ->
        Cont N Q refusalRead ->
          Cont visibleRead refusalRead rootRead ->
            UnaryHistory visibleRead ∧ UnaryHistory refusalRead ∧ UnaryHistory rootRead ∧
              hsame H (append Z S) ∧ Cont (append Z S) Q visibleRead ∧
                Cont N Q refusalRead ∧ Cont visibleRead refusalRead rootRead ∧
                  Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet visibleRoute refusalRoute rootRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have visibleUnary : UnaryHistory visibleRead :=
    unary_cont_closed unaryAppend unaryQ visibleRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed visibleUnary refusalUnary rootRoute
  exact
    ⟨visibleUnary, refusalUnary, rootUnary, sameH, visibleRoute, refusalRoute,
      rootRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
