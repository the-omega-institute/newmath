import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalLineWitnessPhaseRealSourceTotality [AskSetup] [PackageSetup]
    {Z S M R Q H C P N phaseRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H phaseRead ->
        SemanticNameCert
            (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row phaseRead)
            (fun row : BHist => UnaryHistory row ∧ Cont Q H phaseRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧
            UnaryHistory phaseRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier phaseRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed unaryQ unaryH phaseRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row phaseRead)
          (fun row : BHist => UnaryHistory row ∧ Cont Q H phaseRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro phaseRead
        ⟨hsame_refl phaseRead, phaseUnary⟩
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
      exact ⟨source.right, phaseRoute⟩
  }
  exact ⟨cert, unaryZ, unaryS, unaryQ, phaseUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
