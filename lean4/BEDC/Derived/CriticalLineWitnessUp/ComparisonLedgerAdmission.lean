import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_comparison_ledger_admission
    {Z S M R Q H C P N comparisonRead publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H comparisonRead ->
        Cont comparisonRead C publicRead ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Q ∨ hsame row H ∨ hsame row C ∨
                  Cont Q H comparisonRead ∨ Cont comparisonRead C publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont Q H comparisonRead ∧
                  Cont comparisonRead C publicRead)
              hsame ∧ UnaryHistory comparisonRead ∧ UnaryHistory publicRead ∧
            hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet comparisonRoute publicRoute
  obtain ⟨unaryQ, unaryC, _unaryN, sameH⟩ :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryQ unaryH comparisonRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed comparisonUnary unaryC publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row H ∨ hsame row C ∨ Cont Q H comparisonRead ∨
              Cont comparisonRead C publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q H comparisonRead ∧ Cont comparisonRead C publicRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr publicRoute)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, comparisonRoute, publicRoute⟩
  }
  exact ⟨cert, comparisonUnary, publicUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
