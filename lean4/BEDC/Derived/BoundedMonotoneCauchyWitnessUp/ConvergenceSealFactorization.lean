import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_factorization [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      convergenceRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow provenance convergenceRead →
        Cont convergenceRead regular completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory convergenceRead ∧
                  UnaryHistory completionRead ∧ Cont source schedule regular ∧
                    Cont regular witness trap ∧ Cont trap sealRow route ∧
                      Cont sealRow provenance convergenceRead ∧
                        Cont convergenceRead regular completionRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sealProvenanceConvergence convergenceRegularCompletion completionPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceConvergence
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed convergenceUnary regularUnary convergenceRegularCompletion
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, convergenceUnary, completionUnary, sourceScheduleRegular, regularWitnessTrap,
      trapSealRoute, sealProvenanceConvergence, convergenceRegularCompletion, provenancePkg,
      completionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
