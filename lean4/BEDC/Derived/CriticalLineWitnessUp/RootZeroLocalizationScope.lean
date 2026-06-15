import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zero_localization_scope
    {Z S M R Q H C P N zeroRead heightWindow boundedRead ledgerRead publicRead scopeRead :
      BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zeroRead →
        Cont M Q heightWindow →
          Cont heightWindow zeroRead boundedRead →
            Cont boundedRead H ledgerRead →
              Cont ledgerRead C publicRead →
                Cont publicRead N scopeRead →
                  UnaryHistory zeroRead ∧ UnaryHistory heightWindow ∧
                    UnaryHistory boundedRead ∧ UnaryHistory ledgerRead ∧
                      UnaryHistory publicRead ∧ UnaryHistory scopeRead ∧
                        hsame H (append Z S) ∧ Cont Z S zeroRead ∧
                          Cont M Q heightWindow ∧
                            Cont heightWindow zeroRead boundedRead ∧
                              Cont boundedRead H ledgerRead ∧
                                Cont ledgerRead C publicRead ∧
                                  Cont publicRead N scopeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zeroRoute heightRoute boundedRoute ledgerRoute publicRoute scopeRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZero : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryHeight : UnaryHistory heightWindow :=
    unary_cont_closed unaryM unaryQ heightRoute
  have unaryBounded : UnaryHistory boundedRead :=
    unary_cont_closed unaryHeight unaryZero boundedRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryLedger : UnaryHistory ledgerRead :=
    unary_cont_closed unaryBounded unaryH ledgerRoute
  have unaryC : UnaryHistory C :=
    routeClosure.right.left
  have unaryPublic : UnaryHistory publicRead :=
    unary_cont_closed unaryLedger unaryC publicRoute
  have unaryN : UnaryHistory N :=
    routeClosure.right.right.left
  have unaryScope : UnaryHistory scopeRead :=
    unary_cont_closed unaryPublic unaryN scopeRoute
  exact
    ⟨unaryZero, unaryHeight, unaryBounded, unaryLedger, unaryPublic, unaryScope, sameH,
      zeroRoute, heightRoute, boundedRoute, ledgerRoute, publicRoute, scopeRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
