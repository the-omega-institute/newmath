import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorL10RealStreamOutputFactorization [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont continuation output streamRead →
        PkgSig bundle streamRead pkg →
          UnaryHistory continuation ∧ UnaryHistory output ∧ UnaryHistory streamRead ∧
            Cont continuation output streamRead ∧ hsame transport (append audit continuation) ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle streamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier continuationOutputStream streamPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, _auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed continuationUnary outputUnary continuationOutputStream
  exact
    ⟨continuationUnary, outputUnary, streamUnary, continuationOutputStream,
      transportAuditContinuation, provenancePkg, streamPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
