import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessPrimeZetaDependencyRoute
    {Z S M R Q H C P N primeRead zetaRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zetaRead →
        Cont M R primeRead →
          Cont N Q refusalRead →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row primeRead ∨ hsame row zetaRead ∨ hsame row refusalRead)
                (fun row : BHist => UnaryHistory row)
                (fun _row : BHist =>
                  Cont M R primeRead ∧ Cont Z S zetaRead ∧ Cont N Q refusalRead)
                hsame ∧
              UnaryHistory primeRead ∧ UnaryHistory zetaRead ∧
                UnaryHistory refusalRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute primeRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have primeUnary : UnaryHistory primeRead :=
    unary_cont_closed unaryM unaryR primeRoute
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row primeRead ∨ hsame row zetaRead ∨ hsame row refusalRead)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist =>
            Cont M R primeRead ∧ Cont Z S zetaRead ∧ Cont N Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro primeRead (Or.inl (hsame_refl primeRead))
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
        cases source with
        | inl primeSame =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) primeSame)
        | inr sourceTail =>
            cases sourceTail with
            | inl zetaSame =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) zetaSame))
            | inr refusalSame =>
                exact Or.inr
                  (Or.inr (hsame_trans (hsame_symm sameRows) refusalSame))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl primeSame =>
          exact unary_transport primeUnary (hsame_symm primeSame)
      | inr sourceTail =>
          cases sourceTail with
          | inl zetaSame =>
              exact unary_transport zetaUnary (hsame_symm zetaSame)
          | inr refusalSame =>
              exact unary_transport refusalUnary (hsame_symm refusalSame)
    ledger_sound := by
      intro _row _source
      exact ⟨primeRoute, zetaRoute, refusalRoute⟩
  }
  exact ⟨cert, primeUnary, zetaUnary, refusalUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
