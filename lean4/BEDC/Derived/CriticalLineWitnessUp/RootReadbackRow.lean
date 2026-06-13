import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_readback_row
    {Z S M R Q H C P N readbackSource readbackSupport : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S readbackSource ->
        Cont H N readbackSupport ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
              UnaryHistory N ∧ UnaryHistory readbackSource ∧
                UnaryHistory readbackSupport ∧ hsame H (append Z S) ∧
                  Cont Z S readbackSource ∧ Cont H N readbackSupport := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet readbackSourceRoute readbackSupportRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryReadbackSource : UnaryHistory readbackSource :=
    unary_cont_closed unaryZ unaryS readbackSourceRoute
  have unaryReadbackSupport : UnaryHistory readbackSupport :=
    unary_cont_closed unaryH unaryN readbackSupportRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryP, unaryN,
      unaryReadbackSource, unaryReadbackSupport, sameH, readbackSourceRoute,
      readbackSupportRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
