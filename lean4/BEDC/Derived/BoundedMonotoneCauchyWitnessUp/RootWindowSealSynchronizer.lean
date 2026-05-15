import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_window_seal_synchronizer [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead tailRead criterionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead ledger tailRead →
          Cont tailRead witness criterionRead →
            Cont criterionRead sealRow realRead →
              PkgSig bundle realRead pkg →
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory ledger ∧
                  UnaryHistory sealRow ∧ UnaryHistory windowRead ∧ UnaryHistory tailRead ∧
                    UnaryHistory criterionRead ∧ UnaryHistory realRead ∧
                      Cont source schedule windowRead ∧ Cont windowRead ledger tailRead ∧
                        Cont tailRead witness criterionRead ∧
                          Cont criterionRead sealRow realRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sourceScheduleWindow windowLedgerTail tailWitnessCriterion criterionSealReal
    realPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerTail
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed tailUnary witnessUnary tailWitnessCriterion
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealReal
  exact
    ⟨sourceUnary, scheduleUnary, ledgerUnary, sealUnary, windowUnary, tailUnary,
      criterionUnary, realUnary, sourceScheduleWindow, windowLedgerTail,
      tailWitnessCriterion, criterionSealReal, provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
