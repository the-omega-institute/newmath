import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_window_exactness
    {Z S M R Q H C P N modulusRead comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont modulusRead Q comparisonRead ->
          SemanticNameCert
              (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row modulusRead ∨
                  hsame row comparisonRead)
              (fun row : BHist => hsame row comparisonRead ∧ Cont modulusRead Q comparisonRead)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory modulusRead ∧
              UnaryHistory comparisonRead ∧ Cont M R Q ∧ Cont M R modulusRead ∧
                Cont modulusRead Q comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet modulusRoute comparisonRoute
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, _routeC,
    _routeN⟩ := packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed modulusReadUnary unaryQ comparisonRoute
  have sourceComparison :
      (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row) comparisonRead := by
    exact ⟨hsame_refl comparisonRead, comparisonReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row modulusRead ∨
            hsame row comparisonRead)
        (fun row : BHist => hsame row comparisonRead ∧ Cont modulusRead Q comparisonRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro comparisonRead sourceComparison
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
        exact ⟨source.left, comparisonRoute⟩
    }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, modulusReadUnary, comparisonReadUnary, routeQ,
      modulusRoute, comparisonRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
