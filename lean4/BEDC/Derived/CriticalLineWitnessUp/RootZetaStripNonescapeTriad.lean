import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zeta_strip_nonescape_triad
    {Z S M R Q H C P N zetaRead modulusRead refusalRead zetaBoundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q modulusRead ->
          Cont N Q refusalRead ->
            Cont modulusRead refusalRead zetaBoundary ->
              SemanticNameCert
                  (fun row : BHist => hsame row zetaBoundary ∧ UnaryHistory row)
                  (fun row : BHist => hsame row zetaBoundary)
                  (fun row : BHist =>
                    hsame row zetaBoundary ∧ Cont modulusRead refusalRead zetaBoundary)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧
                  UnaryHistory zetaRead ∧ UnaryHistory modulusRead ∧
                    UnaryHistory refusalRead ∧ UnaryHistory zetaBoundary ∧
                      hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                        Cont zetaRead Q modulusRead ∧ Cont N Q refusalRead ∧
                          Cont modulusRead refusalRead zetaBoundary := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute modulusRoute refusalRoute boundaryRoute
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
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed zetaUnary unaryQ modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory zetaBoundary :=
    unary_cont_closed modulusUnary refusalUnary boundaryRoute
  have sourceAtBoundary : hsame zetaBoundary zetaBoundary ∧ UnaryHistory zetaBoundary :=
    ⟨hsame_refl zetaBoundary, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zetaBoundary ∧ UnaryHistory row)
          (fun row : BHist => hsame row zetaBoundary)
          (fun row : BHist =>
            hsame row zetaBoundary ∧ Cont modulusRead refusalRead zetaBoundary)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zetaBoundary sourceAtBoundary
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
      exact ⟨source.left, boundaryRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, zetaUnary, modulusUnary, refusalUnary,
      boundaryUnary, sameH, zetaRoute, modulusRoute, refusalRoute, boundaryRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
