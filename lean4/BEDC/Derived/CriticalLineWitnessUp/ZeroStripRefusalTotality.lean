import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_refusal_totality
    {Z S M R Q H C P N zeroStripRead refusalRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont N Q refusalRead ->
          Cont refusalRead C boundaryRead ->
            SemanticNameCert
                (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row boundaryRead ∧ Cont Z S zeroStripRead ∧
                    Cont N Q refusalRead)
                (fun row : BHist =>
                  hsame row boundaryRead ∧ Cont refusalRead C boundaryRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory C ∧
                UnaryHistory N ∧ UnaryHistory zeroStripRead ∧
                  UnaryHistory refusalRead ∧ UnaryHistory boundaryRead ∧
                    hsame H (append Z S) ∧ Cont Z S zeroStripRead ∧
                      Cont N Q refusalRead ∧ Cont refusalRead C boundaryRead ∧
                        Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute refusalRoute boundaryRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have zeroUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed refusalUnary unaryC boundaryRoute
  have sourceAtBoundary : hsame boundaryRead boundaryRead ∧ UnaryHistory boundaryRead :=
    ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont Z S zeroStripRead ∧ Cont N Q refusalRead)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont refusalRead C boundaryRead)
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
      exact ⟨source.left, zeroRoute, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundaryRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryC, unaryN, zeroUnary, refusalUnary,
      boundaryUnary, sameH, zeroRoute, refusalRoute, boundaryRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
