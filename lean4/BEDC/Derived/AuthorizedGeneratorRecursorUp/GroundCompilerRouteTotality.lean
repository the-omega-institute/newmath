import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorGroundCompilerRouteTotality [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead auditRead boundaryRead compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
      transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead continuation auditRead ->
          Cont auditRead boundary boundaryRead ->
            Cont boundaryRead localCert compilerRead ->
              PkgSig bundle compilerRead pkg ->
                UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
                  UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
                    UnaryHistory audit ∧ UnaryHistory boundary ∧ UnaryHistory localCert ∧
                      UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                        UnaryHistory boundaryRead ∧ UnaryHistory compilerRead ∧
                          Cont signature eliminator motive ∧ Cont motive branch descent ∧
                            Cont descent output audit ∧ Cont output audit outputRead ∧
                              Cont outputRead continuation auditRead ∧
                                Cont auditRead boundary boundaryRead ∧
                                  Cont boundaryRead localCert compilerRead ∧
                                    hsame transport (append audit continuation) ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle compilerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditRead outputContinuationAudit auditBoundaryRead boundaryNameCompiler
    compilerPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, continuationUnary, provenanceUnary,
    boundaryUnary, localCertUnary, signatureEliminatorMotive, motiveBranchDescent,
    descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary continuationUnary outputContinuationAudit
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed auditReadUnary boundaryUnary auditBoundaryRead
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed boundaryReadUnary localCertUnary boundaryNameCompiler
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, boundaryUnary, localCertUnary, outputReadUnary, auditReadUnary,
      boundaryReadUnary, compilerReadUnary, signatureEliminatorMotive, motiveBranchDescent,
      descentOutputAudit, outputAuditRead, outputContinuationAudit, auditBoundaryRead,
      boundaryNameCompiler, transportAuditContinuation, provenancePkg, compilerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
