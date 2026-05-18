import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootCarrierRoute [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert carrierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont audit boundary carrierRead ->
        PkgSig bundle carrierRead pkg ->
          UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
            UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
              UnaryHistory audit ∧ UnaryHistory boundary ∧ UnaryHistory carrierRead ∧
                Cont signature eliminator motive ∧ Cont motive branch descent ∧
                  Cont descent output audit ∧ Cont audit boundary carrierRead ∧
                    hsame transport (append audit continuation) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle carrierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier auditBoundaryCarrier carrierPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    boundaryUnary, _localCertUnary, signatureEliminatorMotive, motiveBranchDescent,
    descentOutputAudit, transportSameAuditContinuation, provenancePkg⟩ := carrier
  have carrierReadUnary : UnaryHistory carrierRead :=
    unary_cont_closed auditUnary boundaryUnary auditBoundaryCarrier
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, boundaryUnary, carrierReadUnary, signatureEliminatorMotive,
      motiveBranchDescent, descentOutputAudit, auditBoundaryCarrier,
      transportSameAuditContinuation, provenancePkg, carrierPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
