import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_strip_zeta_gamma_source_lock
    {Z S M R Q H C P N zetaRead stripRead gammaRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead H stripRead ->
          Cont stripRead P gammaRead ->
            Cont gammaRead Q modulusRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row P ∨
                      hsame row Q ∨ hsame row modulusRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Z S zetaRead ∧ Cont zetaRead H stripRead ∧
                      Cont stripRead P gammaRead ∧ Cont gammaRead Q modulusRead)
                  hsame ∧
                UnaryHistory zetaRead ∧ UnaryHistory stripRead ∧ UnaryHistory gammaRead ∧
                  UnaryHistory modulusRead ∧ hsame H (append Z S) ∧
                    Cont Z S zetaRead ∧ Cont zetaRead H stripRead ∧
                      Cont stripRead P gammaRead ∧ Cont gammaRead Q modulusRead ∧
                        Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory append
  intro packet zetaRoute stripRoute gammaRoute modulusRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, _unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed zetaUnary unaryH stripRoute
  have gammaUnary : UnaryHistory gammaRead :=
    unary_cont_closed stripUnary unaryP gammaRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed gammaUnary routeClosure.left modulusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row H ∨ hsame row P ∨ hsame row Q ∨
              hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zetaRead ∧ Cont zetaRead H stripRead ∧
              Cont stripRead P gammaRead ∧ Cont gammaRead Q modulusRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead ⟨hsame_refl modulusRead, modulusUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zetaRoute, stripRoute, gammaRoute, modulusRoute⟩
  }
  exact
    ⟨cert, zetaUnary, stripUnary, gammaUnary, modulusUnary, sameH, zetaRoute, stripRoute,
      gammaRoute, modulusRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
