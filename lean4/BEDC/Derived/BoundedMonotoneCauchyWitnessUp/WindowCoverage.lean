import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_coverage [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead witness modulusRead →
          UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
            UnaryHistory windowRead ∧ UnaryHistory modulusRead ∧
              Cont source schedule windowRead ∧ Cont windowRead witness modulusRead ∧
                Cont source schedule regular ∧ Cont regular witness trap ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleWindow windowWitnessModulus
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessModulus
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, windowUnary, modulusUnary, sourceScheduleWindow,
      windowWitnessModulus, sourceScheduleRegular, regularWitnessTrap, provenancePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
