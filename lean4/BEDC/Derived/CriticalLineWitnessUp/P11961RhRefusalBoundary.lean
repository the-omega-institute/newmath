import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_p11961_rh_refusal_boundary
    {Z S M R Q H C P N zeroStripRead comparisonRead refusalBoundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont M R comparisonRead ->
          Cont zeroStripRead comparisonRead refusalBoundary ->
            SemanticNameCert
                (fun row : BHist => hsame row refusalBoundary ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row refusalBoundary ∧ Cont Z S zeroStripRead ∧
                    Cont M R comparisonRead)
                (fun row : BHist =>
                  hsame row refusalBoundary ∧ Cont zeroStripRead comparisonRead refusalBoundary)
                hsame ∧
              UnaryHistory zeroStripRead ∧ UnaryHistory comparisonRead ∧
                UnaryHistory refusalBoundary ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute comparisonRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have zeroUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have refusalUnary : UnaryHistory refusalBoundary :=
    unary_cont_closed zeroUnary comparisonUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusalBoundary ∧ Cont Z S zeroStripRead ∧ Cont M R comparisonRead)
          (fun row : BHist =>
            hsame row refusalBoundary ∧ Cont zeroStripRead comparisonRead refusalBoundary)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusalBoundary ⟨hsame_refl refusalBoundary, refusalUnary⟩
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
      exact ⟨source.left, zeroRoute, comparisonRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute⟩
  }
  exact
    ⟨cert, zeroUnary, comparisonUnary, refusalUnary, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
