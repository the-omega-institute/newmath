import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

/-!
# BoundedMonotoneCauchyWitnessUp terminal source equalizer.
-/

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_terminal_source_equalizer
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      convergenceRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont sealRow provenance convergenceRead ->
        Cont convergenceRead source terminalRead ->
          PkgSig bundle convergenceRead pkg ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory source /\ UnaryHistory trap /\ UnaryHistory convergenceRead /\
                UnaryHistory terminalRead /\ Cont trap sealRow route /\
                  Cont sealRow provenance convergenceRead /\
                    Cont convergenceRead source terminalRead /\
                      PkgSig bundle provenance pkg /\ PkgSig bundle convergenceRead pkg /\
                        PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sealProvenanceConvergence convergenceSourceTerminal convergenceReadPkg
    terminalReadPkg
  obtain ⟨sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have convergenceReadUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceConvergence
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed convergenceReadUnary sourceUnary convergenceSourceTerminal
  exact
    ⟨sourceUnary, trapUnary, convergenceReadUnary, terminalReadUnary, trapSealRoute,
      sealProvenanceConvergence, convergenceSourceTerminal, provenancePkg, convergenceReadPkg,
      terminalReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
