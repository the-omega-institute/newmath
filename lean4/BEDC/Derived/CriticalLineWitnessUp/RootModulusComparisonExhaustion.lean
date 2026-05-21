import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_modulus_comparison_exhaustion
    {Z S M R Q H C P N modulusRead comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont modulusRead Q comparisonRead ->
          SemanticNameCert
              (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
                  hsame row P ∨ hsame row N ∨ hsame row modulusRead ∨
                    hsame row comparisonRead)
              (fun row : BHist => hsame row comparisonRead ∧ Cont modulusRead Q comparisonRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory modulusRead ∧
                UnaryHistory comparisonRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont M R modulusRead ∧ Cont modulusRead Q comparisonRead ∧ Cont Q H C ∧
                    Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet modulusRoute comparisonRoute
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
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed modulusUnary unaryQ comparisonRoute
  have sourceAtComparison : hsame comparisonRead comparisonRead ∧ UnaryHistory comparisonRead :=
    ⟨hsame_refl comparisonRead, comparisonUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row modulusRead ∨
                hsame row comparisonRead)
          (fun row : BHist => hsame row comparisonRead ∧ Cont modulusRead Q comparisonRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro comparisonRead sourceAtComparison
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, comparisonRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, modulusUnary,
      comparisonUnary, sameH, routeQ, modulusRoute, comparisonRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
