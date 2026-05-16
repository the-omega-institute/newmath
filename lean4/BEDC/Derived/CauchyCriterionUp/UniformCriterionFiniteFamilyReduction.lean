import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_uniformcriterion_finite_family_reduction [AskSetup]
    [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint uniformWindow uniformModulus uniformTolerance uniformLedger uniformRegseq
      uniformSeal reductionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      hsame window uniformWindow ->
        hsame modulus uniformModulus ->
          hsame tolerance uniformTolerance ->
            hsame ledger uniformLedger ->
              hsame regseq uniformRegseq ->
                hsame realSeal uniformSeal ->
                  Cont uniformModulus uniformTolerance uniformLedger ->
                    Cont uniformLedger uniformRegseq reductionRead ->
                      PkgSig bundle reductionRead pkg ->
                        UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                          UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
                            UnaryHistory uniformWindow ∧ UnaryHistory uniformModulus ∧
                              UnaryHistory uniformTolerance ∧ UnaryHistory uniformLedger ∧
                                UnaryHistory uniformRegseq ∧ UnaryHistory uniformSeal ∧
                                  Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                                    Cont uniformModulus uniformTolerance uniformLedger ∧
                                      Cont uniformLedger uniformRegseq reductionRead ∧
                                        hsame window uniformWindow ∧
                                          hsame modulus uniformModulus ∧
                                            hsame tolerance uniformTolerance ∧
                                              hsame ledger uniformLedger ∧
                                                hsame regseq uniformRegseq ∧
                                                  hsame realSeal uniformSeal ∧
                                                    PkgSig bundle endpoint pkg ∧
                                                      PkgSig bundle reductionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameWindow sameModulus sameTolerance sameLedger sameRegseq sameRealSeal
    uniformReductionLedger reductionReadRoute reductionReadPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have uniformWindowUnary : UnaryHistory uniformWindow :=
    unary_transport windowUnary sameWindow
  have uniformModulusUnary : UnaryHistory uniformModulus :=
    unary_transport modulusUnary sameModulus
  have uniformToleranceUnary : UnaryHistory uniformTolerance :=
    unary_transport toleranceUnary sameTolerance
  have uniformLedgerUnary : UnaryHistory uniformLedger :=
    unary_transport ledgerUnary sameLedger
  have uniformRegseqUnary : UnaryHistory uniformRegseq :=
    unary_transport regseqUnary sameRegseq
  have uniformSealUnary : UnaryHistory uniformSeal :=
    unary_transport realSealUnary sameRealSeal
  have _reductionReadUnary : UnaryHistory reductionRead :=
    unary_cont_closed uniformLedgerUnary uniformRegseqUnary reductionReadRoute
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
      uniformWindowUnary, uniformModulusUnary, uniformToleranceUnary, uniformLedgerUnary,
      uniformRegseqUnary, uniformSealUnary, windowModulusTolerance, toleranceLedgerRegseq,
      uniformReductionLedger, reductionReadRoute, sameWindow, sameModulus, sameTolerance,
      sameLedger, sameRegseq, sameRealSeal, endpointPkg, reductionReadPkg⟩

end BEDC.Derived.CauchyCriterionUp
