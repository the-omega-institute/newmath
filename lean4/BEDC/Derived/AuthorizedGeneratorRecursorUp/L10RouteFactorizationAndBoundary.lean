import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRegSeqRatRouteFactorization [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont continuation output regseqRead →
        PkgSig bundle regseqRead pkg →
          UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
            UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
              UnaryHistory audit ∧ UnaryHistory continuation ∧ UnaryHistory regseqRead ∧
                Cont signature eliminator motive ∧ Cont motive branch descent ∧
                  Cont descent output audit ∧ Cont continuation output regseqRead ∧
                    hsame transport (append audit continuation) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle regseqRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier continuationOutputRegseq regseqPkg
  rcases carrier with
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, _transportUnary, continuationUnary, _provenanceUnary, _boundaryUnary,
      _localCertUnary, signatureEliminatorMotive, motiveBranchDescent, descentOutputAudit,
      transportAuditContinuation, provenancePkg⟩
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed continuationUnary outputUnary continuationOutputRegseq
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, continuationUnary, regseqUnary, signatureEliminatorMotive,
      motiveBranchDescent, descentOutputAudit, continuationOutputRegseq,
      transportAuditContinuation, provenancePkg, regseqPkg⟩

theorem AuthorizedGeneratorRecursorRegSeqRatRouteStrictObstruction [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert regseqRead blockedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont continuation output regseqRead →
        PkgSig bundle regseqRead pkg →
          Cont regseqRead boundary blockedRead →
            UnaryHistory boundary →
              UnaryHistory regseqRead ∧ UnaryHistory blockedRead ∧
                Cont continuation output regseqRead ∧ Cont regseqRead boundary blockedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle regseqRead pkg ∧
                    hsame transport (append audit continuation) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier continuationOutputRegseq regseqPkg regseqBoundaryBlocked boundaryUnary
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, _auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed continuationUnary outputUnary continuationOutputRegseq
  have blockedUnary : UnaryHistory blockedRead :=
    unary_cont_closed regseqUnary boundaryUnary regseqBoundaryBlocked
  exact
    ⟨regseqUnary, blockedUnary, continuationOutputRegseq, regseqBoundaryBlocked,
      provenancePkg, regseqPkg, transportAuditContinuation⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
