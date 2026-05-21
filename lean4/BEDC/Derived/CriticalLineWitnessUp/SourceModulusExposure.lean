import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_modulus_exposure
    {Z S M R Q H C P N sourceRead modulusRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N -> Cont Z S sourceRead ->
      Cont M R modulusRead -> Cont sourceRead modulusRead boundaryRead ->
        SemanticNameCert
            (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row boundaryRead ∧ Cont Z S sourceRead ∧ Cont M R modulusRead)
            (fun row : BHist =>
              hsame row boundaryRead ∧ Cont sourceRead modulusRead boundaryRead)
            hsame ∧
          UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧ UnaryHistory boundaryRead ∧
            hsame H (append Z S) ∧ Cont M R Q := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute boundaryRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sourceUnary modulusUnary boundaryRoute
  have sourceAtBoundary : hsame boundaryRead boundaryRead ∧ UnaryHistory boundaryRead :=
    ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont Z S sourceRead ∧ Cont M R modulusRead)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont sourceRead modulusRead boundaryRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceAtBoundary
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
      exact ⟨source.left, sourceRoute, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundaryRoute⟩
  }
  exact ⟨cert, sourceUnary, modulusUnary, boundaryUnary, sameH, routeQ⟩

theorem CriticalLineWitnessSourceModulusExposure
    {Z S M R Q H C P N sourceRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R modulusRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧ Cont Z S sourceRead ∧
              Cont M R modulusRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro packet sourceRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, sourceUnary, modulusUnary, sourceRoute,
      modulusRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
