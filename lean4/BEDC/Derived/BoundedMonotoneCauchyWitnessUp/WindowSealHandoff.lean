import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_seal_handoff [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert convergenceRead diagonalRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow provenance convergenceRead →
        Cont convergenceRead route diagonalRead →
          Cont diagonalRead route handoffRead →
            PkgSig bundle handoffRead pkg →
              UnaryHistory diagonalRead ∧ UnaryHistory handoffRead ∧
                Cont trap sealRow route ∧ Cont sealRow provenance convergenceRead ∧
                  Cont convergenceRead route diagonalRead ∧ Cont diagonalRead route handoffRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier convergenceRoute diagonalRoute handoffRoute handoffPkg
  rcases carrier with
    ⟨_sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
      sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
      _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary convergenceRoute
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed convergenceUnary (unary_cont_closed _trapUnary sealUnary trapSealRoute)
      diagonalRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed diagonalUnary (unary_cont_closed _trapUnary sealUnary trapSealRoute)
      handoffRoute
  exact
    ⟨diagonalUnary, handoffUnary, trapSealRoute, convergenceRoute, diagonalRoute,
      handoffRoute, provenancePkg, handoffPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
