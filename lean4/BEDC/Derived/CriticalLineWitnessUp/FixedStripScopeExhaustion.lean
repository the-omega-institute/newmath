import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_scope_exhaustion
    {Z S M R Q H C P N stripRead modulusRead scopeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont M R modulusRead ->
          Cont stripRead modulusRead scopeRead ->
            SemanticNameCert
                (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row scopeRead ∧ Cont Z S stripRead ∧
                  Cont M R modulusRead)
                (fun row : BHist => hsame row scopeRead ∧ Cont stripRead modulusRead scopeRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory scopeRead ∧ hsame H (append Z S) ∧ Cont Z S stripRead ∧
                    Cont M R Q ∧ Cont M R modulusRead ∧ Cont stripRead modulusRead scopeRead ∧
                      Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert CriticalLineWitnessCarrier
  intro packet stripRoute modulusRoute scopeRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed stripUnary modulusUnary scopeRoute
  have sourceAtScope : hsame scopeRead scopeRead ∧ UnaryHistory scopeRead :=
    ⟨hsame_refl scopeRead, scopeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row scopeRead ∧ Cont Z S stripRead ∧
            Cont M R modulusRead)
          (fun row : BHist => hsame row scopeRead ∧ Cont stripRead modulusRead scopeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead sourceAtScope
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
      exact ⟨source.left, stripRoute, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, scopeRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, stripUnary, modulusUnary, scopeUnary,
      sameH, stripRoute, routeQ, modulusRoute, scopeRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
