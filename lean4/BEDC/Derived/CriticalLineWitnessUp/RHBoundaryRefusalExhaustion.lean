import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_boundary_refusal_exhaustion
    {Z S M R Q H C P N sourceRead sourceNormal refusalRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead M sourceNormal ->
          Cont N Q refusalRead ->
            Cont sourceNormal refusalRead boundaryRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist => hsame row boundaryRead ∧ Cont Z S sourceRead)
                  (fun row : BHist =>
                    hsame row boundaryRead ∧ Cont sourceNormal refusalRead boundaryRead)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory sourceNormal ∧
                  UnaryHistory refusalRead ∧ UnaryHistory boundaryRead ∧
                    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute sourceNormalRoute refusalRoute boundaryRoute
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
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have sourceNormalUnary : UnaryHistory sourceNormal :=
    unary_cont_closed sourceUnary unaryM sourceNormalRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sourceNormalUnary refusalUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row boundaryRead ∧ Cont Z S sourceRead)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont sourceNormal refusalRead boundaryRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead
        ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact ⟨source.left, sourceRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundaryRoute⟩
  }
  exact
    ⟨cert, sourceUnary, sourceNormalUnary, refusalUnary, boundaryUnary, sameH, routeQ,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
