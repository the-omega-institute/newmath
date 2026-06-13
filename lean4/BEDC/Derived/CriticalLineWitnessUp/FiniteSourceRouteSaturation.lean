import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_finite_source_route_saturation
    {Z S M R Q H C P N sourceRead modulusRead finalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R modulusRead ->
          Cont sourceRead modulusRead finalRead ->
            SemanticNameCert
                (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row sourceRead ∨ hsame row modulusRead ∨ hsame row finalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S sourceRead ∧ Cont M R modulusRead ∧
                    Cont sourceRead modulusRead finalRead)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧ UnaryHistory finalRead ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute finalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, _routeQ, routeC, routeN⟩ :=
    packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed sourceReadUnary modulusReadUnary finalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row sourceRead ∨ hsame row modulusRead ∨ hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S sourceRead ∧ Cont M R modulusRead ∧
              Cont sourceRead modulusRead finalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalRead ⟨hsame_refl finalRead, finalReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, modulusRoute, finalRoute⟩
  }
  exact ⟨cert, sourceReadUnary, modulusReadUnary, finalReadUnary, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
