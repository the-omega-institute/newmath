import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRouteRefusal [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert refused gate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont boundary localCert refused ->
        Cont refused audit gate ->
          PkgSig bundle gate pkg ->
            UnaryHistory boundary ∧ UnaryHistory localCert ∧ UnaryHistory refused ∧
              UnaryHistory gate ∧ Cont boundary localCert refused ∧ Cont refused audit gate ∧
                hsame transport (append audit continuation) ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle gate pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  intro carrier boundaryLocalRefused refusedAuditGate gatePkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    _outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportSameAuditContinuation, provenancePkg⟩ := carrier
  have refusedUnary : UnaryHistory refused :=
    unary_cont_closed boundaryUnary localCertUnary boundaryLocalRefused
  have gateUnary : UnaryHistory gate :=
    unary_cont_closed refusedUnary auditUnary refusedAuditGate
  exact
    ⟨boundaryUnary, localCertUnary, refusedUnary, gateUnary, boundaryLocalRefused,
      refusedAuditGate, transportSameAuditContinuation, provenancePkg, gatePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
