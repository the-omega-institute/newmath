import BEDC.Derived.AuthorizedGeneratorRecursorUp.ReadinessRoute
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorReadinessRoute_root_totality_strict_obstruction
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert generator compiler refusal replay terminalRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorReadinessRoute signature eliminator motive branch descent output
        audit transport continuation provenance boundary localCert generator compiler refusal replay
        bundle pkg →
      Cont output continuation terminalRead →
        PkgSig bundle terminalRead pkg →
          UnaryHistory terminalRead ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localCert pkg ∧ PkgSig bundle terminalRead pkg ∧
              (Cont terminalRead (BHist.e0 hostTail) output → False) ∧
                (Cont terminalRead (BHist.e1 hostTail) output → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro readiness outputContinuation terminalPkg
  rcases readiness with
    ⟨carrier, _signatureGenerator, _generatorCompiler, _boundaryRefusal,
      _transportReplay, provenancePkg, localCertPkg⟩
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, _auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, _transportAuditContinuation, _carrierProvenancePkg⟩
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed outputUnary continuationUnary outputContinuation
  have e0Obstruction : Cont terminalRead (BHist.e0 hostTail) output → False :=
    (cont_mutual_extension_right_tail_absurd
      (h := output) (k := terminalRead) (leftTail := continuation) (rightTail := hostTail)).left
      outputContinuation
  have e1Obstruction : Cont terminalRead (BHist.e1 hostTail) output → False :=
    (cont_mutual_extension_right_tail_absurd
      (h := output) (k := terminalRead) (leftTail := continuation) (rightTail := hostTail)).right
      outputContinuation
  exact
    ⟨terminalUnary, provenancePkg, localCertPkg, terminalPkg, e0Obstruction,
      e1Obstruction⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
