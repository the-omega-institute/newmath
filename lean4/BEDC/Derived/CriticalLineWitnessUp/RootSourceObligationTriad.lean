import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_obligation_triad
    {Z S M R Q H C P N rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z M rootRead →
        SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row rootRead)
              (fun row : BHist => hsame row rootRead ∧ Cont Z M rootRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory rootRead ∧
              hsame H (append Z S) ∧ Cont Z M rootRead ∧ Cont Q H C ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet rootRoute
  obtain ⟨unaryZ, unaryS, unaryM, _unaryR, _unaryP, sameH, _routeQ, routeC, routeN⟩ :=
    packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryZ unaryM rootRoute
  have sourceRoot : hsame rootRead rootRead ∧ UnaryHistory rootRead :=
    ⟨hsame_refl rootRead, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row rootRead)
          (fun row : BHist => hsame row rootRead ∧ Cont Z M rootRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceRoot
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, rootRoute⟩
  }
  exact ⟨cert, unaryZ, unaryS, unaryM, rootUnary, sameH, rootRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
