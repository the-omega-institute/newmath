import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_tail_window_service [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead serviceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule tailRead ->
        Cont tailRead witness serviceRead ->
          PkgSig bundle serviceRead pkg ->
            UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
              UnaryHistory tailRead ∧ UnaryHistory serviceRead ∧
                Cont source schedule tailRead ∧ Cont tailRead witness serviceRead ∧
                  Cont source schedule regular ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle serviceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleTail tailWitnessService servicePkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have serviceUnary : UnaryHistory serviceRead :=
    unary_cont_closed tailUnary witnessUnary tailWitnessService
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, tailUnary, serviceUnary, sourceScheduleTail,
      tailWitnessService, sourceScheduleRegular, provenancePkg, servicePkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
