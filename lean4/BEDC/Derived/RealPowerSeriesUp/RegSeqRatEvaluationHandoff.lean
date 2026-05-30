import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_regseqrat_evaluation_handoff [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N regBudget endpointRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M regBudget ->
        Cont regBudget E endpointRead ->
          Cont endpointRead C terminalRead ->
            PkgSig bundle regBudget pkg ->
              PkgSig bundle terminalRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row W ∨ hsame row S ∨ hsame row M ∨
                        hsame row E ∨ hsame row regBudget ∨ hsame row endpointRead ∨
                          hsame row terminalRead)
                    (fun row : BHist =>
                      PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg ∧
                        hsame row terminalRead)
                    hsame ∧
                  UnaryHistory regBudget ∧ UnaryHistory endpointRead ∧
                    UnaryHistory terminalRead ∧ Cont S M regBudget ∧
                      Cont regBudget E endpointRead ∧ Cont endpointRead C terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier budgetRoute endpointRoute terminalRoute _budgetPkg terminalPkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, _RUnary, _WUnary, SUnary, MUnary, EUnary,
    _HUnary, CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, provenancePkg⟩ := carrier
  have regBudgetUnary : UnaryHistory regBudget :=
    unary_cont_closed SUnary MUnary budgetRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed regBudgetUnary EUnary endpointRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed endpointUnary CUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row W ∨ hsame row S ∨ hsame row M ∨
              hsame row E ∨ hsame row regBudget ∨ hsame row endpointRead ∨
                hsame row terminalRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg ∧
              hsame row terminalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead
        ⟨hsame_refl terminalRead, terminalUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, terminalPkg, source.left⟩
  }
  exact
    ⟨cert, regBudgetUnary, endpointUnary, terminalUnary, budgetRoute, endpointRoute,
      terminalRoute⟩

end BEDC.Derived.RealPowerSeriesUp
