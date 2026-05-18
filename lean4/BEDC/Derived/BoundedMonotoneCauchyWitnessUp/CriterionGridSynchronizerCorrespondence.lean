import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_criterion_grid_synchronizer_correspondence
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail gridSeal criterionRead synchronizerRead
      observationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      UnaryHistory gridBudget →
        UnaryHistory gridClassifier →
          UnaryHistory gridSeal →
            Cont sealRow gridBudget gridLedger →
              Cont gridLedger gridClassifier gridTail →
                Cont gridTail gridSeal criterionRead →
                  Cont criterionRead witness synchronizerRead →
                    Cont synchronizerRead localCert observationRead →
                      PkgSig bundle criterionRead pkg →
                        PkgSig bundle synchronizerRead pkg →
                          PkgSig bundle observationRead pkg →
                            UnaryHistory source ∧ UnaryHistory schedule ∧
                              UnaryHistory witness ∧ UnaryHistory sealRow ∧
                                UnaryHistory gridBudget ∧ UnaryHistory gridLedger ∧
                                  UnaryHistory gridClassifier ∧ UnaryHistory gridTail ∧
                                    UnaryHistory gridSeal ∧ UnaryHistory criterionRead ∧
                                      UnaryHistory synchronizerRead ∧
                                        UnaryHistory observationRead ∧
                                          Cont sealRow gridBudget gridLedger ∧
                                            Cont gridLedger gridClassifier gridTail ∧
                                              Cont gridTail gridSeal criterionRead ∧
                                                Cont criterionRead witness synchronizerRead ∧
                                                  Cont synchronizerRead localCert
                                                    observationRead ∧
                                                    PkgSig bundle provenance pkg ∧
                                                      PkgSig bundle criterionRead pkg ∧
                                                        PkgSig bundle synchronizerRead pkg ∧
                                                          PkgSig bundle observationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier gridBudgetUnary gridClassifierUnary gridSealUnary sealGridBudget
    gridLedgerClassifier gridTailSeal criterionWitnessSynchronizer
    synchronizerLocalObservation criterionPkg synchronizerPkg observationPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have localCertUnary : UnaryHistory localCert :=
    (unary_cont_factors_from_result transportLocalRoute routeUnary).right
  have gridLedgerUnary : UnaryHistory gridLedger :=
    unary_cont_closed sealUnary gridBudgetUnary sealGridBudget
  have gridTailUnary : UnaryHistory gridTail :=
    unary_cont_closed gridLedgerUnary gridClassifierUnary gridLedgerClassifier
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed gridTailUnary gridSealUnary gridTailSeal
  have synchronizerUnary : UnaryHistory synchronizerRead :=
    unary_cont_closed criterionUnary witnessUnary criterionWitnessSynchronizer
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed synchronizerUnary localCertUnary synchronizerLocalObservation
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, sealUnary, gridBudgetUnary, gridLedgerUnary,
      gridClassifierUnary, gridTailUnary, gridSealUnary, criterionUnary, synchronizerUnary,
      observationUnary, sealGridBudget, gridLedgerClassifier, gridTailSeal,
      criterionWitnessSynchronizer, synchronizerLocalObservation, provenancePkg, criterionPkg,
      synchronizerPkg, observationPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
