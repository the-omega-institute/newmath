import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_uniform_criterion_handoff
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      uniformIndex uniformWindow uniformModulus uniformTail uniformSeal rootRead criterionRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      UnaryHistory uniformIndex →
        UnaryHistory uniformWindow →
          UnaryHistory uniformModulus →
            UnaryHistory uniformTail →
              UnaryHistory uniformSeal →
                Cont source schedule rootRead →
                  Cont rootRead uniformIndex criterionRead →
                    PkgSig bundle criterionRead pkg →
                      UnaryHistory rootRead ∧ UnaryHistory criterionRead ∧
                        Cont source schedule rootRead ∧
                          Cont rootRead uniformIndex criterionRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle criterionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier uniformIndexUnary _uniformWindowUnary _uniformModulusUnary _uniformTailUnary
    _uniformSealUnary sourceScheduleRoot rootIndexCriterion criterionPkg
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRoot
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed rootUnary uniformIndexUnary rootIndexCriterion
  exact
    ⟨rootUnary, criterionUnary, sourceScheduleRoot, rootIndexCriterion, provenancePkg,
      criterionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
