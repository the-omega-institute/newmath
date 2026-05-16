import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_selector_factorization [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead witnessRead trapRead realRead selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule windowRead ->
        Cont windowRead regular witnessRead ->
          Cont witnessRead ledger trapRead ->
            Cont trapRead sealRow realRead ->
              Cont realRead provenance selectorRead ->
                PkgSig bundle selectorRead pkg ->
                  UnaryHistory windowRead ∧ UnaryHistory witnessRead ∧
                    UnaryHistory trapRead ∧ UnaryHistory realRead ∧
                      UnaryHistory selectorRead ∧ Cont source schedule windowRead ∧
                        Cont windowRead regular witnessRead ∧ Cont witnessRead ledger trapRead ∧
                          Cont trapRead sealRow realRead ∧
                            Cont realRead provenance selectorRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory BoundedMonotoneCauchyWitnessCarrier
  intro carrier sourceScheduleWindow windowRegularWitness witnessLedgerTrap trapSealReal
    realProvenanceSelector selectorPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowUnary regularUnary windowRegularWitness
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed witnessReadUnary ledgerUnary witnessLedgerTrap
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed trapReadUnary sealUnary trapSealReal
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed realReadUnary provenanceUnary realProvenanceSelector
  exact
    ⟨windowUnary, witnessReadUnary, trapReadUnary, realReadUnary, selectorReadUnary,
      sourceScheduleWindow, windowRegularWitness, witnessLedgerTrap, trapSealReal,
      realProvenanceSelector, provenancePkg, selectorPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
