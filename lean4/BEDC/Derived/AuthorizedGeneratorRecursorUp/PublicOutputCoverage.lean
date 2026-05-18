import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorPublicOutputCoverage [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert readiness normalizationRead closedSubstitutionRead compilerRead publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit readiness ->
        Cont readiness continuation normalizationRead ->
          Cont readiness boundary closedSubstitutionRead ->
            Cont readiness provenance compilerRead ->
              Cont normalizationRead closedSubstitutionRead publicRead ->
                PkgSig bundle publicRead pkg ->
                  UnaryHistory readiness ∧ UnaryHistory normalizationRead ∧
                    UnaryHistory closedSubstitutionRead ∧ UnaryHistory compilerRead ∧
                      UnaryHistory publicRead ∧ hsame transport (append audit continuation) ∧
                        Cont output audit readiness ∧
                          Cont readiness continuation normalizationRead ∧
                            Cont readiness boundary closedSubstitutionRead ∧
                              Cont readiness provenance compilerRead ∧
                                Cont normalizationRead closedSubstitutionRead publicRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro carrier outputAuditReadiness readinessContinuationNormalization
    readinessBoundaryClosedSubstitution readinessProvenanceCompiler
    normalizationClosedSubstitutionPublic publicPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, transportUnary, continuationUnary, provenanceUnary,
      boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportSame, provenancePkg⟩
  have readinessUnary : UnaryHistory readiness :=
    unary_cont_closed outputUnary auditUnary outputAuditReadiness
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed readinessUnary continuationUnary readinessContinuationNormalization
  have closedSubstitutionUnary : UnaryHistory closedSubstitutionRead :=
    unary_cont_closed readinessUnary boundaryUnary readinessBoundaryClosedSubstitution
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed readinessUnary provenanceUnary readinessProvenanceCompiler
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed normalizationUnary closedSubstitutionUnary
      normalizationClosedSubstitutionPublic
  exact
    ⟨readinessUnary, normalizationUnary, closedSubstitutionUnary, compilerUnary,
      publicUnary, transportSame, outputAuditReadiness, readinessContinuationNormalization,
      readinessBoundaryClosedSubstitution, readinessProvenanceCompiler,
      normalizationClosedSubstitutionPublic, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
