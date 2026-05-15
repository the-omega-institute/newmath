import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_seal_public_route_exhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      convergenceRead criterionTail realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont sealRow provenance convergenceRead ->
        Cont regular witness criterionTail ->
          Cont criterionTail sealRow convergenceRead ->
            Cont convergenceRead provenance realSealRead ->
              PkgSig bundle convergenceRead pkg ->
                PkgSig bundle realSealRead pkg ->
                  UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                    UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                      UnaryHistory sealRow ∧ UnaryHistory provenance ∧
                        UnaryHistory convergenceRead ∧ UnaryHistory criterionTail ∧
                          UnaryHistory realSealRead ∧ Cont sealRow provenance convergenceRead ∧
                            Cont regular witness criterionTail ∧
                              Cont criterionTail sealRow convergenceRead ∧
                                Cont convergenceRead provenance realSealRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle convergenceRead pkg ∧
                                      PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sealProvenanceConvergence regularWitnessCriterion criterionSealConvergence
    convergenceProvenanceReal convergencePkg realSealPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceConvergence
  have criterionUnary : UnaryHistory criterionTail :=
    unary_cont_closed regularUnary witnessUnary regularWitnessCriterion
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed convergenceUnary provenanceUnary convergenceProvenanceReal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, provenanceUnary, convergenceUnary, criterionUnary, realSealUnary,
      sealProvenanceConvergence, regularWitnessCriterion, criterionSealConvergence,
      convergenceProvenanceReal, provenancePkg, convergencePkg, realSealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
