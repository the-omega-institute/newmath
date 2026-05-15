import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_tail_real_seal_route_totality [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      tailRead sealRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule tailRead →
        Cont tailRead witness sealRead →
          Cont sealRead sealRow realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory witness ∧
                UnaryHistory sealRow ∧ UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory realRead ∧ Cont source schedule tailRead ∧
                    Cont tailRead witness sealRead ∧ Cont sealRead sealRow realRead ∧
                      Cont source schedule regular ∧ Cont regular witness trap ∧
                        Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier sourceScheduleTail tailWitnessSeal sealRealRead realReadPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary witnessUnary tailWitnessSeal
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed sealReadUnary sealUnary sealRealRead
  exact
    ⟨sourceUnary, scheduleUnary, witnessUnary, sealUnary, tailUnary, sealReadUnary,
      realReadUnary, sourceScheduleTail, tailWitnessSeal, sealRealRead, sourceScheduleRegular,
      regularWitnessTrap, trapSealRoute, provenancePkg, realReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
