import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_source_to_seal_triad
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule sourceRead ->
        Cont sourceRead witness tailRead ->
          Cont tailRead sealRow sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                UnaryHistory sealRow ∧ UnaryHistory sourceRead ∧ UnaryHistory tailRead ∧
                  UnaryHistory sealRead ∧ Cont source schedule sourceRead ∧
                    Cont sourceRead witness tailRead ∧ Cont tailRead sealRow sealRead ∧
                      Cont source schedule regular ∧ Cont regular witness trap ∧
                        Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleRead readWitnessTail tailSealRead sealPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceReadUnary witnessUnary readWitnessTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailReadUnary sealUnary tailSealRead
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, sealUnary, sourceReadUnary, tailReadUnary,
      sealReadUnary, sourceScheduleRead, readWitnessTail, tailSealRead, sourceScheduleRegular,
      regularWitnessTrap, trapSealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
