import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_readiness_triad
    {Z S M R Q H C P N zetaRead sourceRead refusalRead readyRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead H sourceRead ->
          Cont N Q refusalRead ->
            Cont sourceRead refusalRead readyRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row readyRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row readyRead ∧ Cont Z S zetaRead ∧
                      Cont zetaRead H sourceRead)
                  (fun row : BHist =>
                    hsame row readyRead ∧ Cont sourceRead refusalRead readyRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
                  UnaryHistory zetaRead ∧ UnaryHistory sourceRead ∧
                    UnaryHistory refusalRead ∧ UnaryHistory readyRead ∧
                      hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
                        Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute sourceRoute refusalRoute readyRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryRoot : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryRoot (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed zetaUnary unaryH sourceRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have readyUnary : UnaryHistory readyRead :=
    unary_cont_closed sourceUnary refusalUnary readyRoute
  have sourceAtReady : hsame readyRead readyRead ∧ UnaryHistory readyRead :=
    ⟨hsame_refl readyRead, readyUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readyRead ∧ Cont Z S zetaRead ∧ Cont zetaRead H sourceRead)
          (fun row : BHist =>
            hsame row readyRead ∧ Cont sourceRead refusalRead readyRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readyRead sourceAtReady
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
      exact ⟨source.left, zetaRoute, sourceRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, readyRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryH, zetaUnary, sourceUnary, refusalUnary,
      readyUnary, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
