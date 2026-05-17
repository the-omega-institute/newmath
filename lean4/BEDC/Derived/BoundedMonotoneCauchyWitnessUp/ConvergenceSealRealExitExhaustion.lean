import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_real_exit_exhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      convergenceRead finiteRead selectorRead criterionRead realRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow provenance convergenceRead →
        Cont convergenceRead ledger finiteRead →
          Cont finiteRead witness selectorRead →
            Cont selectorRead regular criterionRead →
              Cont criterionRead sealRow realRead →
                Cont realRead transport terminalRead →
                  PkgSig bundle terminalRead pkg →
                    UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                      UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory sealRow ∧
                        UnaryHistory convergenceRead ∧ UnaryHistory finiteRead ∧
                          UnaryHistory selectorRead ∧ UnaryHistory criterionRead ∧
                            UnaryHistory realRead ∧ UnaryHistory terminalRead ∧
                              Cont sealRow provenance convergenceRead ∧
                                Cont convergenceRead ledger finiteRead ∧
                                  Cont finiteRead witness selectorRead ∧
                                    Cont selectorRead regular criterionRead ∧
                                      Cont criterionRead sealRow realRead ∧
                                        Cont realRead transport terminalRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sealProvenanceConvergence convergenceLedgerFinite finiteWitnessSelector
    selectorRegularCriterion criterionSealReal realTransportTerminal terminalPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have transportUnary : UnaryHistory transport :=
    (unary_cont_factors_from_result transportLocalCertRoute routeUnary).left
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceConvergence
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed convergenceUnary ledgerUnary convergenceLedgerFinite
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed finiteUnary witnessUnary finiteWitnessSelector
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed selectorUnary regularUnary selectorRegularCriterion
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealReal
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed realUnary transportUnary realTransportTerminal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, sealUnary,
      convergenceUnary, finiteUnary, selectorUnary, criterionUnary, realUnary, terminalUnary,
      sealProvenanceConvergence, convergenceLedgerFinite, finiteWitnessSelector,
      selectorRegularCriterion, criterionSealReal, realTransportTerminal, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
