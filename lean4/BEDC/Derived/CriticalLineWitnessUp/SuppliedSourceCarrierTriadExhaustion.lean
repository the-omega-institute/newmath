import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_supplied_source_carrier_triad_exhaustion
    {Z S M R Q H C P N sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S sourceRead →
        SemanticNameCert
            (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row sourceRead)
            (fun row : BHist => hsame row sourceRead ∧ Cont Z S sourceRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory sourceRead ∧
            hsame H (append Z S) ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute
  obtain ⟨unaryZ, unaryS, unaryQ, sameH, routeC, routeN⟩ :=
    CriticalLineWitnessCarrier_root_source_triad packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have sourceAtSourceRead : hsame sourceRead sourceRead ∧ UnaryHistory sourceRead :=
    ⟨hsame_refl sourceRead, sourceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row sourceRead)
          (fun row : BHist => hsame row sourceRead ∧ Cont Z S sourceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceAtSourceRead
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
      exact ⟨source.left, sourceRoute⟩
  }
  exact ⟨cert, unaryZ, unaryS, unaryQ, sourceUnary, sameH, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
