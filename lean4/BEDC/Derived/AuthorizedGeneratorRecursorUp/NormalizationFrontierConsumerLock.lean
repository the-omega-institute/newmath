import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorNormalizationFrontierConsumerLock [AskSetup]
    [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert outputRead frontierRead generatorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output continuation outputRead ->
        Cont outputRead boundary frontierRead ->
          Cont frontierRead localCert generatorRead ->
            PkgSig bundle generatorRead pkg ->
              UnaryHistory outputRead ∧ UnaryHistory frontierRead ∧
                UnaryHistory generatorRead ∧ Cont output continuation outputRead ∧
                  Cont outputRead boundary frontierRead ∧
                    Cont frontierRead localCert generatorRead ∧
                      hsame transport (append audit continuation) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle generatorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputContinuationRead outputReadBoundaryFrontier frontierLocalGenerator
    generatorPkg
  obtain
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, _auditUnary, _transportUnary, continuationUnary, provenanceUnary,
      boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ :=
      carrier
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary continuationUnary outputContinuationRead
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed outputReadUnary boundaryUnary outputReadBoundaryFrontier
  have generatorReadUnary : UnaryHistory generatorRead :=
    unary_cont_closed frontierReadUnary localCertUnary frontierLocalGenerator
  exact
    ⟨outputReadUnary, frontierReadUnary, generatorReadUnary, outputContinuationRead,
      outputReadBoundaryFrontier, frontierLocalGenerator, transportAuditContinuation,
      provenancePkg, generatorPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
