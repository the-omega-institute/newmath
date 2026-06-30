import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_refusal_ledger_nonescape
    {Z S M R Q H C P N refusalRead ledgerRead escapeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont N Q refusalRead →
        Cont refusalRead P ledgerRead →
          Cont ledgerRead H escapeRead →
            SemanticNameCert
                (fun row : BHist => hsame row escapeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row refusalRead ∨ hsame row ledgerRead ∨ hsame row escapeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont N Q refusalRead ∧
                    Cont refusalRead P ledgerRead ∧ Cont ledgerRead H escapeRead ∧
                      hsame row escapeRead)
                hsame ∧
              UnaryHistory refusalRead ∧ UnaryHistory ledgerRead ∧
                UnaryHistory escapeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier refusalRoute ledgerRoute escapeRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed refusalUnary unaryP ledgerRoute
  have escapeUnary : UnaryHistory escapeRead :=
    unary_cont_closed ledgerUnary unaryH escapeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row escapeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusalRead ∨ hsame row ledgerRead ∨ hsame row escapeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont N Q refusalRead ∧ Cont refusalRead P ledgerRead ∧
              Cont ledgerRead H escapeRead ∧ hsame row escapeRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro escapeRead ⟨hsame_refl escapeRead, escapeUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refusalRoute, ledgerRoute, escapeRoute, source.left⟩
  }
  exact ⟨cert, refusalUnary, ledgerUnary, escapeUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
