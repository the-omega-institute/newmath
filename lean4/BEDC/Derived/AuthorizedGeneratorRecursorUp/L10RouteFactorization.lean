import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_regseqrat_route_factorization
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead regSeqRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont output localCert outputRead →
        Cont outputRead continuation regSeqRead →
          Cont regSeqRead boundary publicRead →
            PkgSig bundle publicRead pkg →
              UnaryHistory output ∧ UnaryHistory localCert ∧ UnaryHistory outputRead ∧
                UnaryHistory continuation ∧ UnaryHistory regSeqRead ∧ UnaryHistory boundary ∧
                  UnaryHistory publicRead ∧ Cont output localCert outputRead ∧
                    Cont outputRead continuation regSeqRead ∧
                      Cont regSeqRead boundary publicRead ∧
                        hsame transport (append audit continuation) ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputLocalCertRead outputReadContinuationRegSeq regSeqBoundaryPublic publicPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, _auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary localCertUnary outputLocalCertRead
  have regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed outputReadUnary continuationUnary outputReadContinuationRegSeq
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed regSeqReadUnary boundaryUnary regSeqBoundaryPublic
  exact
    ⟨outputUnary, localCertUnary, outputReadUnary, continuationUnary, regSeqReadUnary,
      boundaryUnary, publicReadUnary, outputLocalCertRead, outputReadContinuationRegSeq,
      regSeqBoundaryPublic, transportAuditContinuation, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
