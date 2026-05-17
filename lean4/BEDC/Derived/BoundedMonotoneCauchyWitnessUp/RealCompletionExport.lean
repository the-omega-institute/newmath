import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_completion_export
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      finiteRead regularRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont schedule ledger finiteRead →
        Cont finiteRead regular regularRead →
          Cont regularRead sealRow completionRead →
            PkgSig bundle finiteRead pkg →
              PkgSig bundle completionRead pkg →
                UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                  UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                    UnaryHistory sealRow ∧ UnaryHistory finiteRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory completionRead ∧
                        Cont schedule ledger finiteRead ∧
                          Cont finiteRead regular regularRead ∧
                            Cont regularRead sealRow completionRead ∧
                              Cont source schedule regular ∧ Cont regular witness trap ∧
                                Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle finiteRead pkg ∧
                                    PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier scheduleLedgerFinite finiteRegularRead regularSealCompletion finitePkg
    completionPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed scheduleUnary ledgerUnary scheduleLedgerFinite
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed finiteUnary regularUnary finiteRegularRead
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed regularReadUnary sealUnary regularSealCompletion
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      finiteUnary, regularReadUnary, completionUnary, scheduleLedgerFinite, finiteRegularRead,
      regularSealCompletion, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      provenancePkg, finitePkg, completionPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
