import BEDC.Derived.ProgrammeStrengthLedgerUp.TasteGate

namespace BEDC.Derived.ProgrammeStrengthLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProgrammeStrengthLedgerCarrier_displayed_route [AskSetup] [PackageSetup]
    {Q S D V B R H C P N report : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProgrammeStrengthLedgerCarrier Q S D V B R H C P N bundle pkg ->
      Cont Q S C ->
        Cont C R report ->
          PkgSig bundle report pkg ->
            UnaryHistory Q ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory V ∧
              UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧
                UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory report ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle report pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier claimStrengthRoute reportRoute reportPkg
  obtain ⟨qUnary, sUnary, dUnary, vUnary, bUnary, rUnary, hUnary, cUnary, pUnary,
    nUnary, _claimStrength, _dependencyStatus, _bridgeRefusal, provenancePkg,
    _namePkg⟩ := carrier
  have displayedUnary : UnaryHistory C :=
    unary_cont_closed qUnary sUnary claimStrengthRoute
  have reportUnary : UnaryHistory report :=
    unary_cont_closed displayedUnary rUnary reportRoute
  exact
    ⟨qUnary, sUnary, dUnary, vUnary, bUnary, rUnary, hUnary, cUnary, pUnary, nUnary,
      reportUnary, provenancePkg, reportPkg⟩

end BEDC.Derived.ProgrammeStrengthLedgerUp
