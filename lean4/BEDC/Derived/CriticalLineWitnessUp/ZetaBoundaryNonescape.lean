import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_boundary_nonescape {Z S M R Q H C P N zetaRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N -> Cont Z S zetaRead ->
      SemanticNameCert
          (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row zetaRead ∨ hsame row H ∨
              hsame row N)
          (fun row : BHist => UnaryHistory row ∧ Cont Z S zetaRead ∧ hsame H (append Z S))
          hsame ∧
        UnaryHistory zetaRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row zetaRead ∨ hsame row H ∨
              hsame row N)
          (fun row : BHist => UnaryHistory row ∧ Cont Z S zetaRead ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zetaRead ⟨hsame_refl zetaRead, zetaUnary⟩
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
      right; right
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zetaRoute, sameH⟩
  }
  exact ⟨cert, zetaUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
