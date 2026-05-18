import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootCarrierAdmission [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert carrierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit carrierRead ->
        PkgSig bundle carrierRead pkg ->
          UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
            UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
              UnaryHistory audit ∧ UnaryHistory carrierRead ∧
                Cont signature eliminator motive ∧ Cont motive branch descent ∧
                  Cont descent output audit ∧ Cont output audit carrierRead ∧
                    hsame transport (append audit continuation) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle carrierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditCarrier carrierPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, signatureEliminatorMotive, motiveBranchDescent,
    descentOutputAudit, transportSameAuditContinuation, provenancePkg⟩ := carrier
  have carrierReadUnary : UnaryHistory carrierRead :=
    unary_cont_closed outputUnary auditUnary outputAuditCarrier
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, carrierReadUnary, signatureEliminatorMotive, motiveBranchDescent,
      descentOutputAudit, outputAuditCarrier, transportSameAuditContinuation, provenancePkg,
      carrierPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
