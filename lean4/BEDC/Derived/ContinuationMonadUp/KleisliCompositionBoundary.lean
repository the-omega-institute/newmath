import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_kleisli_composition_boundary
    {A B C f g u H K L N standardRead : BHist} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N standardRead ->
        SemanticNameCert
          (fun row : BHist => hsame row standardRead ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont A f B ∧ Cont B g C ∧ Cont f g K ∧ Cont K u L ∧
              Cont L N row)
          (fun row : BHist => hsame row standardRead ∧ hsame N L)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame UnaryHistory
  intro carrier standardRoute
  obtain ⟨unaryB, _unaryC, unaryK, unaryL, sameEndpoint⟩ :=
    ContinuationMonadCarrier_route_closure carrier
  obtain ⟨_unaryA, _unaryF, _unaryG, _unaryU, routeB, routeC, routeK, routeL,
    _sameEndpoint⟩ := carrier
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryStandardRead : UnaryHistory standardRead :=
    unary_cont_closed unaryL unaryN standardRoute
  have sourceStandard :
      (fun row : BHist => hsame row standardRead ∧ UnaryHistory row) standardRead := by
    exact ⟨hsame_refl standardRead, unaryStandardRead⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro standardRead sourceStandard
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
      intro row source
      cases source.left
      exact ⟨routeB, routeC, routeK, routeL, standardRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sameEndpoint⟩
  }

end BEDC.Derived.ContinuationMonadUp
