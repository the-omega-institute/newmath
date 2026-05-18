import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_output_route_determinacy [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont audit continuation outputRead →
        PkgSig bundle outputRead pkg →
          UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
            UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
              UnaryHistory audit ∧ UnaryHistory outputRead ∧
                Cont signature eliminator motive ∧ Cont motive branch descent ∧
                  Cont descent output audit ∧ Cont audit continuation outputRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier auditContinuationOutput outputPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, signatureEliminatorMotive, motiveBranchDescent,
    descentOutputAudit, _transportAuditContinuation, provenancePkg⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed auditUnary continuationUnary auditContinuationOutput
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, outputReadUnary, signatureEliminatorMotive, motiveBranchDescent,
      descentOutputAudit, auditContinuationOutput, provenancePkg, outputPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
