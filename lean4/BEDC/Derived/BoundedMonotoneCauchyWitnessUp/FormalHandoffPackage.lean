import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_formal_handoff_route [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      finiteRead regularRead completionRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont schedule ledger finiteRead ->
        Cont finiteRead regular regularRead ->
          Cont regularRead sealRow completionRead ->
            Cont completionRead localCert handoffRead ->
              PkgSig bundle finiteRead pkg ->
                PkgSig bundle completionRead pkg ->
                  PkgSig bundle handoffRead pkg ->
                    UnaryHistory finiteRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory handoffRead ∧
                        Cont schedule ledger finiteRead ∧ Cont finiteRead regular regularRead ∧
                          Cont regularRead sealRow completionRead ∧
                            Cont completionRead localCert handoffRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier scheduleLedgerFinite finiteRegular regularSealCompletion completionLocalHandoff
    _finitePkg _completionPkg handoffPkg
  obtain ⟨_sourceUnary, regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have localCertUnary : UnaryHistory localCert :=
    (unary_cont_factors_from_result transportLocalRoute routeUnary).right
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed scheduleUnary ledgerUnary scheduleLedgerFinite
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed finiteUnary regularUnary finiteRegular
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed regularReadUnary sealUnary regularSealCompletion
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed completionUnary localCertUnary completionLocalHandoff
  exact
    ⟨finiteUnary, regularReadUnary, completionUnary, handoffUnary, scheduleLedgerFinite,
      finiteRegular, regularSealCompletion, completionLocalHandoff, provenancePkg, handoffPkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_formal_handoff_package [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      formalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule regular →
        Cont regular witness trap →
          Cont trap sealRow formalRead →
            PkgSig bundle formalRead pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory formalRead ∧
                    Cont source schedule regular ∧ Cont regular witness trap ∧
                      Cont trap sealRow formalRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle formalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceScheduleRegular regularWitnessTrap trapSealFormal formalPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _carrierSourceScheduleRegular, _carrierRegularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have formalUnary : UnaryHistory formalRead :=
    unary_cont_closed trapUnary sealUnary trapSealFormal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, formalUnary, sourceScheduleRegular, regularWitnessTrap, trapSealFormal,
      provenancePkg, formalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
