import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_source_exhaust_determinacy [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead handoffRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule sourceRead →
        Cont sourceRead regular handoffRead →
          Cont handoffRead witness tailRead →
            Cont tailRead sealRow sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory sourceRead ∧ UnaryHistory handoffRead ∧
                  UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                    Cont source schedule sourceRead ∧
                      Cont sourceRead regular handoffRead ∧
                        Cont handoffRead witness tailRead ∧
                          Cont tailRead sealRow sealRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleRead readRegularHandoff handoffWitnessTail tailSealRead sealPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRead
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed sourceReadUnary regularUnary readRegularHandoff
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed handoffReadUnary witnessUnary handoffWitnessTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailReadUnary sealUnary tailSealRead
  exact
    ⟨sourceReadUnary, handoffReadUnary, tailReadUnary, sealReadUnary, sourceScheduleRead,
      readRegularHandoff, handoffWitnessTail, tailSealRead, provenancePkg, sealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
