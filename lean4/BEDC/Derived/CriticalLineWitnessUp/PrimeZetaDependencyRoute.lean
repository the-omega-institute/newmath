import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_prime_zeta_dependency_route
    {Z S M R Q H C P N zetaRead primeRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zetaRead →
        Cont zetaRead Q primeRead →
          Cont primeRead N refusalRead →
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row refusalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S zetaRead ∧ Cont zetaRead Q primeRead ∧
                    Cont primeRead N refusalRead ∧ hsame H (append Z S))
                hsame ∧
              UnaryHistory zetaRead ∧ UnaryHistory primeRead ∧ UnaryHistory refusalRead ∧
                hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute primeRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    routeClosure.left
  have unaryN : UnaryHistory N :=
    routeClosure.right.right.left
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryPrimeRead : UnaryHistory primeRead :=
    unary_cont_closed unaryZetaRead unaryQ primeRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed unaryPrimeRead unaryN refusalRoute
  have sourceAtRefusal :
      hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, unaryRefusalRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zetaRead ∧ Cont zetaRead Q primeRead ∧
              Cont primeRead N refusalRead ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceAtRefusal
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
      exact ⟨source.right, zetaRoute, primeRoute, refusalRoute, sameH⟩
  }
  exact ⟨cert, unaryZetaRead, unaryPrimeRead, unaryRefusalRead, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
