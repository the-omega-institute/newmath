import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorL10OpenPhaseSourceTriad [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont output localCert sourceRead →
        PkgSig bundle sourceRead pkg →
          UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
            UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
              UnaryHistory audit ∧ UnaryHistory sourceRead ∧ Cont signature eliminator motive ∧
                Cont motive branch descent ∧ Cont descent output audit ∧
                  Cont output localCert sourceRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputLocalSource sourcePkg
  rcases carrier with
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary, _boundaryUnary,
      localCertUnary, signatureEliminatorMotive, motiveBranchDescent, descentOutputAudit,
      _transportAuditContinuation, provenancePkg⟩
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed outputUnary localCertUnary outputLocalSource
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      _auditUnary, sourceUnary, signatureEliminatorMotive, motiveBranchDescent,
      descentOutputAudit, outputLocalSource, provenancePkg, sourcePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
