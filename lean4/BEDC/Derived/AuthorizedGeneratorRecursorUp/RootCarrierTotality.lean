import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootCarrierTotality [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead boundaryRead carrierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead boundary boundaryRead ->
          Cont boundaryRead localCert carrierRead ->
            PkgSig bundle carrierRead pkg ->
              UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
                UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
                  UnaryHistory audit ∧ UnaryHistory boundary ∧ UnaryHistory localCert ∧
                    UnaryHistory outputRead ∧ UnaryHistory boundaryRead ∧
                      UnaryHistory carrierRead ∧ Cont signature eliminator motive ∧
                        Cont motive branch descent ∧ Cont descent output audit ∧
                          Cont output audit outputRead ∧
                            Cont outputRead boundary boundaryRead ∧
                              Cont boundaryRead localCert carrierRead ∧
                                hsame transport (append audit continuation) ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle carrierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier outputAuditRead outputBoundaryRead boundaryLocalCarrier carrierPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    boundaryUnary, localCertUnary, signatureEliminatorMotive, motiveBranchDescent,
    descentOutputAudit, transportSameAuditContinuation, provenancePkg⟩ := carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed outputReadUnary boundaryUnary outputBoundaryRead
  have carrierReadUnary : UnaryHistory carrierRead :=
    unary_cont_closed boundaryReadUnary localCertUnary boundaryLocalCarrier
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, boundaryUnary, localCertUnary, outputReadUnary, boundaryReadUnary,
      carrierReadUnary, signatureEliminatorMotive, motiveBranchDescent, descentOutputAudit,
      outputAuditRead, outputBoundaryRead, boundaryLocalCarrier, transportSameAuditContinuation,
      provenancePkg, carrierPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
