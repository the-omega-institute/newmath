import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_boundary_refusal_totality
    {Z S M R Q H C P N zetaStripRead refusalRead rhBoundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaStripRead ->
        Cont N Q refusalRead ->
          Cont zetaStripRead refusalRead rhBoundary ->
            SemanticNameCert
                (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row zetaStripRead ∨ hsame row refusalRead ∨
                    hsame row rhBoundary ∨ hsame row N ∨ hsame row Q)
                (fun row : BHist =>
                  hsame row rhBoundary ∧ Cont Z S zetaStripRead ∧
                    Cont N Q refusalRead ∧ Cont zetaStripRead refusalRead rhBoundary)
                hsame ∧
              UnaryHistory zetaStripRead ∧ UnaryHistory refusalRead ∧
                UnaryHistory rhBoundary ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaStripRoute refusalRoute boundaryRoute
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
  have zetaStripUnary : UnaryHistory zetaStripRead :=
    unary_cont_closed unaryZ unaryS zetaStripRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory rhBoundary :=
    unary_cont_closed zetaStripUnary refusalUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zetaStripRead ∨ hsame row refusalRead ∨ hsame row rhBoundary ∨
              hsame row N ∨ hsame row Q)
          (fun row : BHist =>
            hsame row rhBoundary ∧ Cont Z S zetaStripRead ∧ Cont N Q refusalRead ∧
              Cont zetaStripRead refusalRead rhBoundary)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhBoundary
        ⟨hsame_refl rhBoundary, boundaryUnary⟩
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
      exact ⟨source.left, zetaStripRoute, refusalRoute, boundaryRoute⟩
  }
  exact ⟨cert, zetaStripUnary, refusalUnary, boundaryUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
