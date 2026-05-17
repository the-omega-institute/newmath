import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_grid_root_package [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      gridBudget gridLedger gridClassifier gridTail streamRead dyadicRead regSeqRead limitRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      UnaryHistory gridBudget →
        UnaryHistory gridClassifier →
          Cont source regular streamRead →
            Cont streamRead ledger dyadicRead →
              Cont dyadicRead witness regSeqRead →
                Cont regSeqRead trap limitRead →
                  Cont limitRead sealRow realRead →
                    Cont realRead gridBudget gridLedger →
                      Cont gridLedger gridClassifier gridTail →
                        PkgSig bundle realRead pkg →
                          PkgSig bundle gridTail pkg →
                            UnaryHistory streamRead ∧ UnaryHistory dyadicRead ∧
                              UnaryHistory regSeqRead ∧ UnaryHistory limitRead ∧
                                UnaryHistory realRead ∧ UnaryHistory gridLedger ∧
                                  UnaryHistory gridTail ∧ Cont source regular streamRead ∧
                                    Cont streamRead ledger dyadicRead ∧
                                      Cont dyadicRead witness regSeqRead ∧
                                        Cont regSeqRead trap limitRead ∧
                                          Cont limitRead sealRow realRead ∧
                                            Cont realRead gridBudget gridLedger ∧
                                              Cont gridLedger gridClassifier gridTail ∧
                                                PkgSig bundle provenance pkg ∧
                                                  PkgSig bundle realRead pkg ∧
                                                    PkgSig bundle gridTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier gridBudgetUnary gridClassifierUnary sourceRegularStream streamLedgerDyadic
    dyadicWitnessRegSeq regSeqTrapLimit limitSealReal realGridBudget gridLedgerClassifier
    realPkg gridTailPkg
  obtain ⟨sourceUnary, regularUnary, _scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularStream
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary ledgerUnary streamLedgerDyadic
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed dyadicUnary witnessUnary dyadicWitnessRegSeq
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed regSeqUnary trapUnary regSeqTrapLimit
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed limitUnary sealUnary limitSealReal
  have gridLedgerUnary : UnaryHistory gridLedger :=
    unary_cont_closed realUnary gridBudgetUnary realGridBudget
  have gridTailUnary : UnaryHistory gridTail :=
    unary_cont_closed gridLedgerUnary gridClassifierUnary gridLedgerClassifier
  exact
    ⟨streamUnary, dyadicUnary, regSeqUnary, limitUnary, realUnary, gridLedgerUnary,
      gridTailUnary, sourceRegularStream, streamLedgerDyadic, dyadicWitnessRegSeq,
      regSeqTrapLimit, limitSealReal, realGridBudget, gridLedgerClassifier, provenancePkg,
      realPkg, gridTailPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
