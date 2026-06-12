import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_refusal_boundary_totality
    {Z S M R Q H C P N zetaStripRead refusalRead rhBoundary consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaStripRead ->
        Cont N Q refusalRead ->
          Cont zetaStripRead refusalRead rhBoundary ->
            Cont rhBoundary C consumerRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row consumerRead ∧ Cont Z S zetaStripRead ∧
                      Cont N Q refusalRead)
                  (fun row : BHist =>
                    hsame row consumerRead ∧ Cont rhBoundary C consumerRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
                  UnaryHistory zetaStripRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory rhBoundary ∧ UnaryHistory consumerRead ∧
                      hsame H (append Z S) ∧ Cont Z S zetaStripRead ∧
                        Cont N Q refusalRead ∧ Cont zetaStripRead refusalRead rhBoundary ∧
                          Cont rhBoundary C consumerRead ∧ Cont M R Q ∧ Cont Q H C ∧
                            Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaStripRoute refusalRoute boundaryRoute consumerRoute
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
  have zetaStripUnary : UnaryHistory zetaStripRead :=
    unary_cont_closed unaryZ unaryS zetaStripRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory rhBoundary :=
    unary_cont_closed zetaStripUnary refusalUnary boundaryRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed boundaryUnary unaryC consumerRoute
  have sourceAtConsumer : hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row consumerRead ∧ Cont Z S zetaStripRead ∧ Cont N Q refusalRead)
          (fun row : BHist => hsame row consumerRead ∧ Cont rhBoundary C consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
      exact ⟨source.left, zetaStripRoute, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryN, zetaStripUnary, refusalUnary, boundaryUnary,
      consumerUnary, sameH, zetaStripRoute, refusalRoute, boundaryRoute, consumerRoute,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
