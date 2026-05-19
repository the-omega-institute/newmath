import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_ledger_route_stability
    {Z S M R Q H C P N ledgerRead comparisonRead stableRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R ledgerRead ->
        Cont ledgerRead Q comparisonRead ->
          Cont comparisonRead H stableRead ->
            SemanticNameCert
                (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row stableRead ∧ Cont M R ledgerRead ∧
                    Cont ledgerRead Q comparisonRead)
                (fun row : BHist => hsame row stableRead ∧ Cont comparisonRead H stableRead)
                hsame ∧
              UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
                UnaryHistory ledgerRead ∧ UnaryHistory comparisonRead ∧
                  UnaryHistory stableRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                    Cont Q H C ∧ Cont C P N ∧ Cont M R ledgerRead ∧
                      Cont ledgerRead Q comparisonRead ∧
                        Cont comparisonRead H stableRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet ledgerRoute comparisonRoute stableRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed unaryM unaryR ledgerRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed ledgerUnary unaryQ comparisonRoute
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed comparisonUnary unaryH stableRoute
  have sourceAtStable : hsame stableRead stableRead ∧ UnaryHistory stableRead :=
    ⟨hsame_refl stableRead, stableUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stableRead ∧ Cont M R ledgerRead ∧
              Cont ledgerRead Q comparisonRead)
          (fun row : BHist => hsame row stableRead ∧ Cont comparisonRead H stableRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stableRead sourceAtStable
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
      exact ⟨source.left, ledgerRoute, comparisonRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, stableRoute⟩
  }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, unaryH, ledgerUnary, comparisonUnary, stableUnary,
      sameH, routeQ, routeC, routeN, ledgerRoute, comparisonRoute, stableRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
