import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_finite_readback_totality
    {Z S M R Q H C P N stripRead sourceRead modulusRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead H sourceRead ->
          Cont sourceRead Q modulusRead ->
            Cont modulusRead N boundaryRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist => hsame row boundaryRead)
                  (fun row : BHist => hsame row boundaryRead ∧ Cont modulusRead N boundaryRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                  UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                    UnaryHistory stripRead ∧ UnaryHistory sourceRead ∧
                      UnaryHistory modulusRead ∧ UnaryHistory boundaryRead ∧
                        hsame H (append Z S) ∧ Cont Z S stripRead ∧
                          Cont stripRead H sourceRead ∧ Cont sourceRead Q modulusRead ∧
                            Cont modulusRead N boundaryRead ∧ Cont M R Q ∧
                              Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute sourceRoute modulusRoute boundaryRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed stripUnary unaryH sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary unaryQ modulusRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed modulusUnary unaryN boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row boundaryRead)
          (fun row : BHist => hsame row boundaryRead ∧ Cont modulusRead N boundaryRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundaryRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, stripUnary,
      sourceUnary, modulusUnary, boundaryUnary, sameH, stripRoute, sourceRoute,
      modulusRoute, boundaryRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
