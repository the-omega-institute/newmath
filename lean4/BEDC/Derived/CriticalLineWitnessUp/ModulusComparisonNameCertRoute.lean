import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_comparison_namecert_route
    {Z S M R Q H C P N comparisonRead namedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont M R comparisonRead →
        Cont comparisonRead H namedRead →
          SemanticNameCert
              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row comparisonRead ∨
                  hsame row namedRead)
              (fun row : BHist => hsame row namedRead ∧ Cont comparisonRead H namedRead)
              hsame ∧
            hsame comparisonRead Q ∧ UnaryHistory comparisonRead ∧
              UnaryHistory namedRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet comparisonRoute namedRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have sameComparisonQ : hsame comparisonRead Q :=
    cont_deterministic comparisonRoute routeQ
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed comparisonUnary unaryH namedRoute
  have sourceAtNamed : hsame namedRead namedRead ∧ UnaryHistory namedRead :=
    ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row comparisonRead ∨ hsame row namedRead)
          (fun row : BHist => hsame row namedRead ∧ Cont comparisonRead H namedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceAtNamed
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
      exact ⟨source.left, namedRoute⟩
  }
  exact ⟨cert, sameComparisonQ, comparisonUnary, namedUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
