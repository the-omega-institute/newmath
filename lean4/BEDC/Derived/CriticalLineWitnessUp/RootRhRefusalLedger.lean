import BEDC.Derived.CriticalLineWitnessUp.RootRhRefusalBoundary
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_rh_refusal_ledger
    {Z S M R Q H C P N zetaStripRead refusalRead rhBoundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaStripRead ->
        Cont N Q refusalRead ->
          Cont zetaStripRead refusalRead rhBoundary ->
            SemanticNameCert
                (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row N ∨
                    hsame row zetaStripRead ∨ hsame row refusalRead ∨ hsame row rhBoundary)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S zetaStripRead ∧ Cont N Q refusalRead ∧
                    Cont zetaStripRead refusalRead rhBoundary)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
                UnaryHistory zetaStripRead ∧ UnaryHistory refusalRead ∧
                  UnaryHistory rhBoundary ∧ hsame H (append Z S) ∧
                    Cont Z S zetaStripRead ∧ Cont N Q refusalRead ∧
                      Cont zetaStripRead refusalRead rhBoundary ∧ Cont M R Q ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaStripRoute refusalRoute boundaryRoute
  have boundary :=
    CriticalLineWitnessCarrier_root_rh_refusal_boundary packet zetaStripRoute refusalRoute
      boundaryRoute
  obtain
    ⟨unaryZ, unaryS, unaryQ, unaryN, zetaStripUnary, refusalUnary, boundaryUnary,
      sameH, routeZeta, routeRefusal, routeBoundary, routeQ, routeC, routeN⟩ := boundary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row N ∨
              hsame row zetaStripRead ∨ hsame row refusalRead ∨ hsame row rhBoundary)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zetaStripRead ∧ Cont N Q refusalRead ∧
              Cont zetaStripRead refusalRead rhBoundary)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro rhBoundary ⟨hsame_refl rhBoundary, boundaryUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeZeta, routeRefusal, routeBoundary⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryN, zetaStripUnary, refusalUnary, boundaryUnary,
      sameH, routeZeta, routeRefusal, routeBoundary, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
