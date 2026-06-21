import BEDC.Derived.FinitePrefixStreamUp.NameCertObligations

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FinitePrefixStreamCarrier_real_completion_budget_route
    {k W D R H C P N windowRead regularRead completionRead : BHist} :
    FinitePrefixStreamCarrier k W D R H C P N →
      Cont k W windowRead →
        Cont windowRead D regularRead →
          Cont regularRead R completionRead →
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                    hsame row regularRead ∨ hsame row completionRead)
                (fun row : BHist =>
                  hsame row completionRead ∧ Cont regularRead R completionRead)
                hsame ∧
              UnaryHistory completionRead ∧ Cont k W windowRead ∧
                Cont windowRead D regularRead ∧ Cont regularRead R completionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute regularRoute completionRoute
  obtain
    ⟨unaryK, unaryW, unaryD, unaryR, _unaryC, _unaryN, _sameH, _routeH, _routeP,
      _packetRegularRoute⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryK unaryW windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary unaryD regularRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed regularUnary unaryR completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row regularRead ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ Cont regularRead R completionRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, completionRoute⟩
  }
  exact ⟨cert, completionUnary, windowRoute, regularRoute, completionRoute⟩

end BEDC.Derived.FinitePrefixStreamUp
