import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zero_localization_selector_exhaustion
    {Z S M R Q H C P N zeroRead heightWindow requestRead boundedRead ledgerRead
      publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont M Q heightWindow ->
          Cont Z S requestRead ->
            Cont heightWindow requestRead boundedRead ->
              Cont boundedRead H ledgerRead ->
                Cont ledgerRead C publicRead ->
                  UnaryHistory zeroRead ∧ UnaryHistory heightWindow ∧
                    UnaryHistory boundedRead ∧ UnaryHistory ledgerRead ∧
                      UnaryHistory publicRead ∧ hsame H (append Z S) ∧
                        Cont Z S zeroRead ∧ Cont M Q heightWindow ∧
                          Cont heightWindow requestRead boundedRead ∧
                            Cont boundedRead H ledgerRead ∧
                              Cont ledgerRead C publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zeroRoute heightRoute requestRoute boundedRoute ledgerRoute publicRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryZeroRead : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryHeightWindow : UnaryHistory heightWindow :=
    unary_cont_closed unaryM unaryQ heightRoute
  have unaryRequestRead : UnaryHistory requestRead :=
    unary_cont_closed unaryZ unaryS requestRoute
  have unaryBoundedRead : UnaryHistory boundedRead :=
    unary_cont_closed unaryHeightWindow unaryRequestRead boundedRoute
  have unaryLedgerRead : UnaryHistory ledgerRead :=
    unary_cont_closed unaryBoundedRead unaryH ledgerRoute
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryLedgerRead unaryC publicRoute
  exact
    ⟨unaryZeroRead, unaryHeightWindow, unaryBoundedRead, unaryLedgerRead, unaryPublicRead,
      sameH, zeroRoute, heightRoute, boundedRoute, ledgerRoute, publicRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
