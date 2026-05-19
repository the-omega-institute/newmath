import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_comparison_route_totality
    {Z S M R Q H C P N comparisonRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R comparisonRead ->
        Cont comparisonRead H ledgerRead ->
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row ledgerRead)
              (fun row : BHist => hsame row ledgerRead ∧ Cont comparisonRead H ledgerRead)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory comparisonRead ∧
                UnaryHistory ledgerRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont M R comparisonRead ∧ Cont comparisonRead H ledgerRead ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet comparisonRoute ledgerRoute
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
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed comparisonUnary unaryH ledgerRoute
  have sourceAtLedger : hsame ledgerRead ledgerRead ∧ UnaryHistory ledgerRead :=
    ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row ledgerRead)
          (fun row : BHist => hsame row ledgerRead ∧ Cont comparisonRead H ledgerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead sourceAtLedger
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerRoute⟩
  }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, comparisonUnary,
      ledgerUnary, sameH, routeQ, comparisonRoute, ledgerRoute, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_modulus_comparison_transport_stability
    {Z S M R Q H C P N Ht Ct comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      hsame H Ht →
        Cont Q Ht Ct →
          Cont Ct P comparisonRead →
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory Ht ∧
              UnaryHistory Ct ∧ UnaryHistory comparisonRead ∧ hsame H (append Z S) ∧
                hsame H Ht ∧ Cont M R Q ∧ Cont Q Ht Ct ∧
                  Cont Ct P comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sameTransport transportedRoute comparisonRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryHt : UnaryHistory Ht :=
    unary_transport unaryH sameTransport
  have unaryCt : UnaryHistory Ct :=
    unary_cont_closed unaryQ unaryHt transportedRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryCt unaryP comparisonRoute
  exact
    ⟨unaryM, unaryR, unaryQ, unaryHt, unaryCt, comparisonUnary, sameH, sameTransport,
      routeQ, transportedRoute, comparisonRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
