import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_modulus_terminal_determinacy
    {Z S M R Q H C P N sourceRead modulusRead terminalRead nameRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R modulusRead ->
          Cont sourceRead modulusRead terminalRead ->
            Cont terminalRead N nameRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row nameRead ∧ Cont Z S sourceRead ∧ Cont M R modulusRead)
                  (fun row : BHist =>
                    hsame row nameRead ∧ Cont terminalRead N nameRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                  UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
                    UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory terminalRead ∧ UnaryHistory nameRead ∧
                        hsame H (append Z S) ∧ Cont Z S sourceRead ∧
                          Cont M R modulusRead ∧ Cont sourceRead modulusRead terminalRead ∧
                            Cont terminalRead N nameRead ∧ Cont M R Q ∧ Cont Q H C ∧
                              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute terminalRoute nameRoute
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
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed sourceReadUnary modulusReadUnary terminalRoute
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed terminalReadUnary unaryN nameRoute
  have sourceAtNameRead : hsame nameRead nameRead ∧ UnaryHistory nameRead :=
    ⟨hsame_refl nameRead, nameReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row nameRead ∧ Cont Z S sourceRead ∧ Cont M R modulusRead)
          (fun row : BHist =>
            hsame row nameRead ∧ Cont terminalRead N nameRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead sourceAtNameRead
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
      exact ⟨source.left, nameRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, sourceReadUnary,
      modulusReadUnary, terminalReadUnary, nameReadUnary, sameH, sourceRoute, modulusRoute,
      terminalRoute, nameRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
