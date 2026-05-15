import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_completion_pullback [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead tailRead criterionRead realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead ledger tailRead →
          Cont tailRead witness criterionRead →
            Cont criterionRead sealRow realRead →
              Cont realRead provenance completionRead →
                PkgSig bundle completionRead pkg →
                  UnaryHistory windowRead ∧ UnaryHistory tailRead ∧
                    UnaryHistory criterionRead ∧ UnaryHistory realRead ∧
                      UnaryHistory completionRead ∧ Cont source schedule windowRead ∧
                        Cont windowRead ledger tailRead ∧
                          Cont tailRead witness criterionRead ∧
                            Cont criterionRead sealRow realRead ∧
                              Cont realRead provenance completionRead ∧
                                Cont source schedule regular ∧ Cont regular witness trap ∧
                                  Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowLedgerTail tailWitnessCriterion
    criterionSealReal realProvenanceCompletion completionPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerTail
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed tailUnary witnessUnary tailWitnessCriterion
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealReal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary provenanceUnary realProvenanceCompletion
  exact
    ⟨windowUnary, tailUnary, criterionUnary, realUnary, completionUnary, sourceScheduleWindow,
      windowLedgerTail, tailWitnessCriterion, criterionSealReal, realProvenanceCompletion,
      sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg, completionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
