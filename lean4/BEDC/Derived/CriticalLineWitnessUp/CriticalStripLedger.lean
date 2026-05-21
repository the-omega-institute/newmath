import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_critical_strip_ledger
    {Z S M R Q H C P N zeroRead stripRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead Q stripRead ->
          Cont stripRead N ledgerRead ->
            SemanticNameCert
                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row ledgerRead ∧ Cont Z S zeroRead ∧ Cont zeroRead Q stripRead)
                (fun row : BHist => hsame row ledgerRead ∧ Cont stripRead N ledgerRead)
                hsame ∧
              UnaryHistory zeroRead ∧ UnaryHistory stripRead ∧ UnaryHistory ledgerRead ∧
                hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute stripRoute ledgerRoute
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
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed zeroUnary unaryQ stripRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed stripUnary unaryN ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row ledgerRead ∧ Cont Z S zeroRead ∧ Cont zeroRead Q stripRead)
          (fun row : BHist => hsame row ledgerRead ∧ Cont stripRead N ledgerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact ⟨source.left, zeroRoute, stripRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerRoute⟩
  }
  exact ⟨cert, zeroUnary, stripUnary, ledgerUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
