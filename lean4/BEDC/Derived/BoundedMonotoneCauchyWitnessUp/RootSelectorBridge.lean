import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_selector_bridge [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      selectorBudget dyadicRead locatedRead realThreshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont schedule ledger selectorBudget →
        Cont selectorBudget witness dyadicRead →
          Cont dyadicRead trap locatedRead →
            Cont locatedRead sealRow realThreshold →
              PkgSig bundle realThreshold pkg →
                UnaryHistory schedule ∧ UnaryHistory ledger ∧ UnaryHistory witness ∧
                  UnaryHistory trap ∧ UnaryHistory sealRow ∧ UnaryHistory selectorBudget ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory locatedRead ∧
                      UnaryHistory realThreshold ∧ Cont schedule ledger selectorBudget ∧
                        Cont selectorBudget witness dyadicRead ∧
                          Cont dyadicRead trap locatedRead ∧
                            Cont locatedRead sealRow realThreshold ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle realThreshold pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier selectorRoute dyadicRoute locatedRoute thresholdRoute thresholdPkg
  obtain ⟨_sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorBudget :=
    unary_cont_closed scheduleUnary ledgerUnary selectorRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed selectorUnary witnessUnary dyadicRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed dyadicUnary trapUnary locatedRoute
  have thresholdUnary : UnaryHistory realThreshold :=
    unary_cont_closed locatedUnary sealUnary thresholdRoute
  exact
    ⟨scheduleUnary, ledgerUnary, witnessUnary, trapUnary, sealUnary, selectorUnary,
      dyadicUnary, locatedUnary, thresholdUnary, selectorRoute, dyadicRoute, locatedRoute,
      thresholdRoute, provenancePkg, thresholdPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
