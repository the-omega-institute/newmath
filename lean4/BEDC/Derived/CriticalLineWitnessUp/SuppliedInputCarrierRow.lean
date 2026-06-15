import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_supplied_input_carrier_row
    {Z S M R Q H C P N suppliedRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N → Cont Z S suppliedRead →
      Cont suppliedRead M modulusRead →
        SemanticNameCert
            (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row suppliedRead ∨
                hsame row modulusRead)
            (fun row : BHist => hsame row modulusRead ∧ Cont suppliedRead M modulusRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory suppliedRead ∧
            UnaryHistory modulusRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet suppliedRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have suppliedUnary : UnaryHistory suppliedRead :=
    unary_cont_closed unaryZ unaryS suppliedRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed suppliedUnary unaryM modulusRoute
  have sourceAtModulusRead : hsame modulusRead modulusRead ∧ UnaryHistory modulusRead :=
    ⟨hsame_refl modulusRead, modulusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row suppliedRead ∨
              hsame row modulusRead)
          (fun row : BHist => hsame row modulusRead ∧ Cont suppliedRead M modulusRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead sourceAtModulusRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, modulusRoute⟩
  }
  exact ⟨cert, unaryZ, unaryS, unaryM, suppliedUnary, modulusUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
