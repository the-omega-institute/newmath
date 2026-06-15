import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_strip_modulus_totality
    {Z S M R Q H C P N stripRead modulusRead zetaRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont M R modulusRead ->
          Cont stripRead modulusRead zetaRead ->
            SemanticNameCert
                (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row stripRead ∨ hsame row modulusRead ∨ hsame row zetaRead ∨
                    hsame row Q)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S stripRead ∧ Cont M R modulusRead ∧
                    Cont stripRead modulusRead zetaRead ∧ Cont M R Q)
                hsame ∧
              UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧ UnaryHistory zetaRead ∧
                hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute zetaRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed stripUnary modulusUnary zetaRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stripRead ∨ hsame row modulusRead ∨ hsame row zetaRead ∨
              hsame row Q)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S stripRead ∧ Cont M R modulusRead ∧
              Cont stripRead modulusRead zetaRead ∧ Cont M R Q)
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, stripRoute, modulusRoute, zetaRoute, routeQ⟩
  }
  exact ⟨cert, stripUnary, modulusUnary, zetaUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
