import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessSiblingDependencyRoute
    {Z S M R Q H C P N zetaSource zeroLocus continuationBoundary witnessRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zetaSource →
        Cont zetaSource Q zeroLocus →
          Cont zeroLocus H continuationBoundary →
            Cont continuationBoundary N witnessRead →
              UnaryHistory zetaSource ∧ UnaryHistory zeroLocus ∧
                UnaryHistory continuationBoundary ∧ UnaryHistory witnessRead ∧
                  hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute zeroRoute continuationRoute witnessRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZetaSource : UnaryHistory zetaSource :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryZeroLocus : UnaryHistory zeroLocus :=
    unary_cont_closed unaryZetaSource unaryQ zeroRoute
  have unaryRoot : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryRoot (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryContinuationBoundary : UnaryHistory continuationBoundary :=
    unary_cont_closed unaryZeroLocus unaryH continuationRoute
  have unaryWitnessRead : UnaryHistory witnessRead :=
    unary_cont_closed unaryContinuationBoundary unaryN witnessRoute
  exact
    ⟨unaryZetaSource, unaryZeroLocus, unaryContinuationBoundary, unaryWitnessRead, sameH⟩

theorem CriticalLineWitnessZetaRhDependencyRoute
    {Z S M R Q H C P N zetaRead zeroRead rhBoundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead R zeroRead ->
          Cont zeroRead C rhBoundaryRead ->
            SemanticNameCert
                (fun row : BHist => hsame row rhBoundaryRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row R ∨ hsame row C ∨
                    hsame row zetaRead ∨ hsame row zeroRead ∨ hsame row rhBoundaryRead)
                (fun row : BHist =>
                  hsame row rhBoundaryRead ∧ Cont Z S zetaRead ∧
                    Cont zetaRead R zeroRead ∧ Cont zeroRead C rhBoundaryRead)
                hsame ∧
              UnaryHistory zetaRead ∧ UnaryHistory zeroRead ∧
                UnaryHistory rhBoundaryRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute zeroRoute rhBoundaryRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed zetaUnary unaryR zeroRoute
  have rhBoundaryUnary : UnaryHistory rhBoundaryRead :=
    unary_cont_closed zeroUnary unaryC rhBoundaryRoute
  have sourceAtBoundary : hsame rhBoundaryRead rhBoundaryRead ∧ UnaryHistory rhBoundaryRead :=
    ⟨hsame_refl rhBoundaryRead, rhBoundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhBoundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row R ∨ hsame row C ∨
              hsame row zetaRead ∨ hsame row zeroRead ∨ hsame row rhBoundaryRead)
          (fun row : BHist =>
            hsame row rhBoundaryRead ∧ Cont Z S zetaRead ∧
              Cont zetaRead R zeroRead ∧ Cont zeroRead C rhBoundaryRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhBoundaryRead sourceAtBoundary
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
      exact ⟨source.left, zetaRoute, zeroRoute, rhBoundaryRoute⟩
  }
  exact ⟨cert, zetaUnary, zeroUnary, rhBoundaryUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
