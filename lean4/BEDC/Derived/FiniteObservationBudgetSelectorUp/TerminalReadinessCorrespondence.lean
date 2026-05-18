import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_readiness_correspondence
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminal sectionRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      Cont R E terminal ->
        Cont terminal E sectionRow ->
          PkgSig bundle sectionRow pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row sectionRow ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row sectionRow ∧ Cont B S W ∧ Cont W D R ∧
                  Cont R E terminal ∧ Cont terminal E sectionRow)
              (fun row : BHist => PkgSig bundle sectionRow pkg ∧ hsame row sectionRow)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier terminalRoute sectionRoute sectionPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, regularRoute,
    _sealRoute, _sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD regularRoute
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryR unaryE terminalRoute
  have unarySection : UnaryHistory sectionRow :=
    unary_cont_closed unaryTerminal unaryE sectionRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sectionRow (And.intro (hsame_refl sectionRow) unarySection)
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, budgetRoute, regularRoute, terminalRoute, sectionRoute⟩
    ledger_sound := by
      intro _row source
      exact And.intro sectionPkg source.left
  }

end BEDC.Derived.FiniteObservationBudgetSelectorUp
