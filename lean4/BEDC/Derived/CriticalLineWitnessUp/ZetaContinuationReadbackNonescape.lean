import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_continuation_readback_nonescape
    {Z S M R Q H C P N zetaRead continuationRead readback : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead C continuationRead ->
          Cont continuationRead N readback ->
            SemanticNameCert
                (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row zetaRead ∨ hsame row continuationRead ∨ hsame row readback)
                (fun row : BHist => hsame row readback ∧ Cont continuationRead N readback)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory zetaRead ∧ UnaryHistory continuationRead ∧
                  UnaryHistory readback ∧ hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                    Cont zetaRead C continuationRead ∧ Cont continuationRead N readback ∧
                      Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute continuationRoute readbackRoute
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
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have continuationUnary : UnaryHistory continuationRead :=
    unary_cont_closed zetaUnary unaryC continuationRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed continuationUnary unaryN readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zetaRead ∨ hsame row continuationRead ∨ hsame row readback)
          (fun row : BHist => hsame row readback ∧ Cont continuationRead N readback)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback ⟨hsame_refl readback, readbackUnary⟩
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
      exact ⟨source.left, readbackRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryC, unaryN, zetaUnary, continuationUnary, readbackUnary,
      sameH, zetaRoute, continuationRoute, readbackRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
