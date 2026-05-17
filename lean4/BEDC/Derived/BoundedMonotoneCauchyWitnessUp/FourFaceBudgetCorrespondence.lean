import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_four_face_budget_correspondence
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      dyadicFace streamFace regseqFace realFace terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont schedule witness streamFace ->
        Cont streamFace ledger dyadicFace ->
          Cont dyadicFace regular regseqFace ->
            Cont regseqFace sealRow realFace ->
              Cont realFace provenance terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory streamFace ∧ UnaryHistory dyadicFace ∧
                    UnaryHistory regseqFace ∧ UnaryHistory realFace ∧
                      UnaryHistory terminal ∧ Cont schedule witness streamFace ∧
                        Cont streamFace ledger dyadicFace ∧
                          Cont dyadicFace regular regseqFace ∧
                            Cont regseqFace sealRow realFace ∧
                              Cont realFace provenance terminal ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier scheduleWitnessStream streamLedgerDyadic dyadicRegularRegseq
    regseqSealReal realProvenanceTerminal terminalPkg
  obtain ⟨_sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary,
    _trapUnary, sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ :=
    carrier
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed scheduleUnary witnessUnary scheduleWitnessStream
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed streamUnary ledgerUnary streamLedgerDyadic
  have regseqUnary : UnaryHistory regseqFace :=
    unary_cont_closed dyadicUnary regularUnary dyadicRegularRegseq
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regseqUnary sealUnary regseqSealReal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed realUnary provenanceUnary realProvenanceTerminal
  exact
    ⟨streamUnary, dyadicUnary, regseqUnary, realUnary, terminalUnary,
      scheduleWitnessStream, streamLedgerDyadic, dyadicRegularRegseq, regseqSealReal,
      realProvenanceTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
