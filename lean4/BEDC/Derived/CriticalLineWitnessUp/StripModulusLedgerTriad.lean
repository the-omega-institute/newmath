import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_strip_modulus_ledger_triad
    {Z S M R Q H C P N stripRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q modulusRead ->
          SemanticNameCert
              (fun row : BHist =>
                (hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row modulusRead) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row modulusRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont Z S stripRead ∧ Cont stripRead Q modulusRead ∧
                  hsame H (append Z S))
              hsame ∧
            UnaryHistory stripRead ∧ UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed stripUnary unaryQ modulusRoute
  have sourceAtModulus :
      (hsame modulusRead S ∨ hsame modulusRead M ∨ hsame modulusRead Q ∨
          hsame modulusRead modulusRead) ∧
        UnaryHistory modulusRead :=
    ⟨Or.inr (Or.inr (Or.inr (hsame_refl modulusRead))), modulusUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row modulusRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S stripRead ∧ Cont stripRead Q modulusRead ∧
              hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead sourceAtModulus
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
        intro row other sameRows source
        have routeMembership :
            hsame other S ∨ hsame other M ∨ hsame other Q ∨ hsame other modulusRead := by
          cases source.left with
          | inl sameS =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameS)
          | inr rest =>
              cases rest with
              | inl sameM =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameM))
              | inr rest =>
                  cases rest with
                  | inl sameQ =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameQ)))
                  | inr sameModulus =>
                      exact Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameModulus)))
        exact ⟨routeMembership, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameS =>
          exact Or.inl sameS
      | inr rest =>
          cases rest with
          | inl sameM =>
              exact Or.inr (Or.inl sameM)
          | inr rest =>
              cases rest with
              | inl sameQ =>
                  exact Or.inr (Or.inr (Or.inl sameQ))
              | inr sameModulus =>
                  exact Or.inr (Or.inr (Or.inr sameModulus))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, stripRoute, modulusRoute, sameH⟩
  }
  exact ⟨cert, stripUnary, modulusUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
