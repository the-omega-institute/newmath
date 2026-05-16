import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_diagonal_readback
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      convergenceRead diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont sealRow provenance convergenceRead ->
        Cont convergenceRead route diagonalRead ->
          PkgSig bundle diagonalRead pkg ->
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory convergenceRead ∧
                  UnaryHistory diagonalRead ∧ Cont source schedule regular ∧
                    Cont regular witness trap ∧ Cont trap sealRow route ∧
                      Cont sealRow provenance convergenceRead ∧
                        Cont convergenceRead route diagonalRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sealProvenanceConvergence convergenceRouteDiagonal diagonalPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceConvergence
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed convergenceUnary routeUnary convergenceRouteDiagonal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, convergenceUnary, diagonalUnary, sourceScheduleRegular, regularWitnessTrap,
      trapSealRoute, sealProvenanceConvergence, convergenceRouteDiagonal, provenancePkg,
      diagonalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
