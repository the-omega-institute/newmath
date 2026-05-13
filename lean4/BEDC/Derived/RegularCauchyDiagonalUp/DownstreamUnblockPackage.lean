import BEDC.Derived.RegularCauchyDiagonalUp.SelectorWindowFunctoriality

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_downstream_unblock_package [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert ratSeed'
      streamWindow' regseqRead' realSeal' windowLedger' provenance' localCert' selectedWindow'
      completionRead' sealRead' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      hsame ratSeed ratSeed' ->
        hsame streamWindow streamWindow' ->
          hsame realSeal realSeal' ->
            hsame localCert localCert' ->
              Cont ratSeed' streamWindow' regseqRead' ->
                Cont regseqRead' realSeal' windowLedger' ->
                  Cont realSeal' localCert' provenance' ->
                    Cont windowLedger' streamWindow' selectedWindow' ->
                      Cont selectedWindow' regseqRead' completionRead' ->
                        Cont regseqRead' realSeal' sealRead' ->
                          Cont realSeal' provenance' endpoint' ->
                            PkgSig bundle provenance' pkg ->
                              PkgSig bundle completionRead' pkg ->
                                PkgSig bundle sealRead' pkg ->
                                  PkgSig bundle endpoint' pkg ->
                                    RegularCauchyDiagonalCarrier ratSeed' streamWindow'
                                        regseqRead' realSeal' windowLedger' provenance'
                                        localCert' bundle pkg ∧
                                      hsame provenance provenance' ∧
                                        UnaryHistory completionRead' ∧
                                          UnaryHistory endpoint' ∧
                                            hsame windowLedger' sealRead' ∧
                                              PkgSig bundle provenance' pkg ∧
                                                PkgSig bundle completionRead' pkg ∧
                                                  PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier ratSeedSame streamWindowSame realSealSame localCertSame regseqReadRow
    windowLedgerRow provenanceRow selectedWindowRow completionRow sealReadRow endpointRow
    provenancePkg completionPkg sealReadPkg endpointPkg
  have source :=
    RegularCauchyDiagonalCarrier_source_stability_obligation carrier ratSeedSame streamWindowSame
      realSealSame localCertSame regseqReadRow windowLedgerRow provenanceRow provenancePkg
  have provenanceSame := source.right.right.right
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary, windowLedgerUnary,
    provenanceUnary, _localCertUnary, _ratStreamRow, regseqSealRow, _sealLocalRow,
    provenancePkgOut⟩ := source.left
  have selectedWindowUnary : UnaryHistory selectedWindow' :=
    unary_cont_closed windowLedgerUnary streamWindowUnary selectedWindowRow
  have completionUnary : UnaryHistory completionRead' :=
    unary_cont_closed selectedWindowUnary regseqReadUnary completionRow
  have sealReadUnary : UnaryHistory sealRead' :=
    unary_cont_closed regseqReadUnary realSealUnary sealReadRow
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed realSealUnary provenanceUnary endpointRow
  have ledgerSameSeal : hsame windowLedger' sealRead' :=
    cont_deterministic regseqSealRow sealReadRow
  exact
    ⟨source.left, provenanceSame, completionUnary, endpointUnary, ledgerSameSeal,
      provenancePkgOut, completionPkg, endpointPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
