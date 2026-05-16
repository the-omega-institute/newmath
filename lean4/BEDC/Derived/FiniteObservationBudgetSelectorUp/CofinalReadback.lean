import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_cofinal_readback
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal cofinal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        Cont terminal H cofinal ->
          PkgSig bundle terminal pkg ->
            PkgSig bundle cofinal pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row cofinal ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row cofinal ∧ Cont B S W ∧ Cont W D R ∧
                      Cont R E terminal ∧ Cont terminal H cofinal)
                  (fun row : BHist =>
                    PkgSig bundle terminal pkg ∧ PkgSig bundle cofinal pkg ∧
                      hsame row cofinal)
                  hsame ∧
                UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧
                  UnaryHistory terminal ∧ UnaryHistory cofinal ∧ Cont B S W ∧
                    Cont W D R ∧ Cont R E terminal ∧ Cont terminal H cofinal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier terminalRoute cofinalRoute terminalPkg cofinalPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, unaryH, budgetSchedule, windowDyadic,
    _carrierSeal, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetSchedule
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD windowDyadic
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unaryCofinal : UnaryHistory cofinal :=
    unary_cont_closed unaryTerminal unaryH cofinalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cofinal ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row cofinal ∧ Cont B S W ∧ Cont W D R ∧
              Cont R E terminal ∧ Cont terminal H cofinal)
          (fun row : BHist =>
            PkgSig bundle terminal pkg ∧ PkgSig bundle cofinal pkg ∧
              hsame row cofinal)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro cofinal ⟨hsame_refl cofinal, unaryCofinal, cofinalPkg⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows sourceRow
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, budgetSchedule, windowDyadic, terminalRoute, cofinalRoute⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨terminalPkg, cofinalPkg, sourceRow.left⟩
    }
  exact
    ⟨cert, unaryW, unaryD, unaryR, unaryE, unaryTerminal, unaryCofinal, budgetSchedule,
      windowDyadic, terminalRoute, cofinalRoute⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
