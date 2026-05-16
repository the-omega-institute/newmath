import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_seal_row_scope [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead witnessRead sealScope : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead witness witnessRead →
          Cont witnessRead sealRow sealScope →
            PkgSig bundle sealScope pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory sealRow ∧ UnaryHistory windowRead ∧
                  UnaryHistory witnessRead ∧ UnaryHistory sealScope ∧
                    Cont source schedule regular ∧ Cont regular witness trap ∧
                      Cont trap sealRow route ∧ Cont source schedule windowRead ∧
                        Cont windowRead witness witnessRead ∧
                          Cont witnessRead sealRow sealScope ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle sealScope pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg
  intro carrier sourceScheduleWindow windowWitnessRead witnessSealScope sealScopePkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessRead
  have sealScopeUnary : UnaryHistory sealScope :=
    unary_cont_closed witnessReadUnary sealUnary witnessSealScope
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, sealUnary, windowUnary,
      witnessReadUnary, sealScopeUnary, sourceScheduleRegular, regularWitnessTrap,
      trapSealRoute, sourceScheduleWindow, windowWitnessRead, witnessSealScope,
      provenancePkg, sealScopePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
