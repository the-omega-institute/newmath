import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_source_ledger_exhaustion
    {Z S M R Q H C P N zeroRead ledgerRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead H ledgerRead ->
          Cont ledgerRead Q downstreamRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory zeroRead ∧ UnaryHistory ledgerRead ∧
                UnaryHistory downstreamRead ∧ hsame H (append Z S) ∧ Cont Z S zeroRead ∧
                  Cont zeroRead H ledgerRead ∧ Cont ledgerRead Q downstreamRead ∧
                    Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zeroRoute ledgerRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryZeroRead : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryLedgerRead : UnaryHistory ledgerRead :=
    unary_cont_closed unaryZeroRead unaryH ledgerRoute
  have unaryDownstreamRead : UnaryHistory downstreamRead :=
    unary_cont_closed unaryLedgerRead unaryQ downstreamRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, unaryH, unaryZeroRead, unaryLedgerRead,
      unaryDownstreamRead, sameH, zeroRoute, ledgerRoute, downstreamRoute, routeQ, routeC,
      routeN⟩

theorem CriticalLineWitnessZeroSourceLedgerExhaustion
    {Z S M R Q H C P N zetaRead comparisonRead publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont M R comparisonRead ->
          Cont zetaRead comparisonRead publicRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory zetaRead ∧ UnaryHistory comparisonRead ∧
                UnaryHistory publicRead ∧ hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                  Cont M R comparisonRead ∧ Cont zetaRead comparisonRead publicRead ∧
                    Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute comparisonRoute publicRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryZetaRead comparisonUnary publicRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryZetaRead, comparisonUnary, publicUnary,
      sameH, zetaRoute, comparisonRoute, publicRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
