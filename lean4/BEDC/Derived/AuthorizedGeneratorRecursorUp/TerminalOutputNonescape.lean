import BEDC.Derived.AuthorizedGeneratorRecursorUp.ReadinessRoute
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalOutputNonescape [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert generator compiler refusal replay terminalRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorReadinessRoute signature eliminator motive branch descent output
        audit transport continuation provenance boundary localCert generator compiler refusal replay
        bundle pkg →
      Cont output continuation terminalRead →
        PkgSig bundle terminalRead pkg →
          UnaryHistory output ∧ UnaryHistory continuation ∧ UnaryHistory terminalRead ∧
            Cont signature eliminator generator ∧ Cont generator compiler output ∧
              Cont boundary audit refusal ∧ Cont transport continuation replay ∧
                Cont output continuation terminalRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localCert pkg ∧ PkgSig bundle terminalRead pkg ∧
                    (Cont terminalRead (BHist.e0 hostTail) output → False) ∧
                      (Cont terminalRead (BHist.e1 hostTail) output → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro route outputContinuationTerminal terminalPkg
  obtain ⟨carrier, signatureEliminatorGenerator, generatorCompilerOutput,
    boundaryAuditRefusal, transportContinuationReplay, provenancePkg, localCertPkg⟩ := route
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    outputUnary, _auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportAuditContinuation, _carrierProvenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed outputUnary continuationUnary outputContinuationTerminal
  have e0Refusal : Cont terminalRead (BHist.e0 hostTail) output → False :=
    fun back => cont_mutual_extension_right_tail_absurd.left outputContinuationTerminal back
  have e1Refusal : Cont terminalRead (BHist.e1 hostTail) output → False :=
    fun back => cont_mutual_extension_right_tail_absurd.right outputContinuationTerminal back
  exact
    ⟨outputUnary, continuationUnary, terminalUnary, signatureEliminatorGenerator,
      generatorCompilerOutput, boundaryAuditRefusal, transportContinuationReplay,
      outputContinuationTerminal, provenancePkg, localCertPkg, terminalPkg, e0Refusal,
      e1Refusal⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
