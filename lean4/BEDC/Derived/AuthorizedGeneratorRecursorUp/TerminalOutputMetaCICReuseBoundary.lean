import BEDC.Derived.AuthorizedGeneratorRecursorUp.ReadinessRoute

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalOutputMetaCICReuseBoundary [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert generator compiler refusal replay terminalRead metacicReuse : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorReadinessRoute signature eliminator motive branch descent output
        audit transport continuation provenance boundary localCert generator compiler refusal replay
        bundle pkg ->
      Cont output continuation terminalRead ->
        Cont terminalRead boundary metacicReuse ->
          PkgSig bundle metacicReuse pkg ->
            UnaryHistory terminalRead ∧ UnaryHistory metacicReuse ∧
              Cont output continuation terminalRead ∧ Cont terminalRead boundary metacicReuse ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg ∧
                  PkgSig bundle metacicReuse pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro route outputTerminal terminalBoundary metacicPkg
  rcases route with
    ⟨carrier, _signatureEliminatorGenerator, _generatorCompilerOutput,
      _boundaryAuditRefusal, _transportContinuationReplay, provenancePkg, localCertPkg⟩
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, _auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, _transportAuditContinuation, _carrierProvenancePkg⟩
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed outputUnary continuationUnary outputTerminal
  have metacicUnary : UnaryHistory metacicReuse :=
    unary_cont_closed terminalUnary boundaryUnary terminalBoundary
  exact
    ⟨terminalUnary, metacicUnary, outputTerminal, terminalBoundary, provenancePkg,
      localCertPkg, metacicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
