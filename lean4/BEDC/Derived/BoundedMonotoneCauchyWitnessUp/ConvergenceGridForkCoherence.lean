import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_grid_fork_coherence
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      convergence grid convergenceSeal gridSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source regular convergence ->
        Cont convergence ledger convergenceSeal ->
          Cont source regular grid ->
            Cont grid ledger gridSeal ->
              PkgSig bundle convergenceSeal pkg ->
                PkgSig bundle gridSeal pkg ->
                  hsame convergenceSeal gridSeal ∧ UnaryHistory convergence ∧
                    UnaryHistory grid ∧ UnaryHistory convergenceSeal ∧ UnaryHistory gridSeal ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle convergenceSeal pkg ∧
                        PkgSig bundle gridSeal pkg := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle PkgSig
  intro carrier sourceRegularConvergence convergenceLedgerSeal sourceRegularGrid
    gridLedgerSeal convergencePkg gridPkg
  obtain ⟨sourceUnary, regularUnary, _scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have convergenceUnary : UnaryHistory convergence :=
    unary_cont_closed sourceUnary regularUnary sourceRegularConvergence
  have gridUnary : UnaryHistory grid :=
    unary_cont_closed sourceUnary regularUnary sourceRegularGrid
  have convergenceSealUnary : UnaryHistory convergenceSeal :=
    unary_cont_closed convergenceUnary ledgerUnary convergenceLedgerSeal
  have gridSealUnary : UnaryHistory gridSeal :=
    unary_cont_closed gridUnary ledgerUnary gridLedgerSeal
  have sameBase : hsame convergence grid :=
    cont_deterministic sourceRegularConvergence sourceRegularGrid
  have convergenceSealFromGrid : Cont grid ledger convergenceSeal := by
    cases sameBase
    exact convergenceLedgerSeal
  have sameSeal : hsame convergenceSeal gridSeal :=
    cont_deterministic convergenceSealFromGrid gridLedgerSeal
  exact
    ⟨sameSeal, convergenceUnary, gridUnary, convergenceSealUnary, gridSealUnary,
      provenancePkg, convergencePkg, gridPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
