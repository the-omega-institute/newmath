import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_cauchy_ledger_readback_exactness
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      cauchyRead criterionRead streamRead dyadicRead regseqRead limitSealRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source regular cauchyRead ->
        Cont cauchyRead schedule criterionRead ->
          Cont criterionRead ledger streamRead ->
            Cont streamRead ledger dyadicRead ->
              Cont dyadicRead regular regseqRead ->
                Cont regseqRead sealRow limitSealRead ->
                  Cont limitSealRead provenance realRead ->
                    PkgSig bundle realRead pkg ->
                      UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                        UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                          UnaryHistory sealRow ∧ UnaryHistory cauchyRead ∧
                            UnaryHistory criterionRead ∧ UnaryHistory streamRead ∧
                              UnaryHistory dyadicRead ∧ UnaryHistory regseqRead ∧
                                UnaryHistory limitSealRead ∧ UnaryHistory realRead ∧
                                  Cont source regular cauchyRead ∧
                                    Cont cauchyRead schedule criterionRead ∧
                                      Cont criterionRead ledger streamRead ∧
                                        Cont streamRead ledger dyadicRead ∧
                                          Cont dyadicRead regular regseqRead ∧
                                            Cont regseqRead sealRow limitSealRead ∧
                                              Cont limitSealRead provenance realRead ∧
                                                PkgSig bundle provenance pkg ∧
                                                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceRegularCauchy cauchyScheduleCriterion criterionLedgerStream
    streamLedgerDyadic dyadicRegularRegseq regseqSealLimit limitProvenanceReal realPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularCauchy
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed cauchyUnary scheduleUnary cauchyScheduleCriterion
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed criterionUnary ledgerUnary criterionLedgerStream
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary ledgerUnary streamLedgerDyadic
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicUnary regularUnary dyadicRegularRegseq
  have limitUnary : UnaryHistory limitSealRead :=
    unary_cont_closed regseqUnary sealUnary regseqSealLimit
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed limitUnary provenanceUnary limitProvenanceReal
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      cauchyUnary, criterionUnary, streamUnary, dyadicUnary, regseqUnary, limitUnary,
      realUnary, sourceRegularCauchy, cauchyScheduleCriterion, criterionLedgerStream,
      streamLedgerDyadic, dyadicRegularRegseq, regseqSealLimit, limitProvenanceReal,
      provenancePkg, realPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
