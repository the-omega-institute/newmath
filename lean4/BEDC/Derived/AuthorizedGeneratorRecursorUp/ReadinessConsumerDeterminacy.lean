import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorReadinessConsumerDeterminacy [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead substRead readiness normalizationRead
      compilerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont B D branchRead →
        Cont branchRead A descentRead →
          Cont descentRead G substRead →
            Cont O A readiness →
              Cont readiness C normalizationRead →
                Cont readiness P compilerRead →
                  Cont normalizationRead substRead publicRead →
                    PkgSig bundle substRead pkg →
                      PkgSig bundle publicRead pkg →
                        UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                          UnaryHistory substRead ∧ UnaryHistory readiness ∧
                            UnaryHistory normalizationRead ∧ UnaryHistory compilerRead ∧
                              UnaryHistory publicRead ∧ Cont B D branchRead ∧
                                Cont branchRead A descentRead ∧ Cont descentRead G substRead ∧
                                  Cont O A readiness ∧ Cont readiness C normalizationRead ∧
                                    Cont readiness P compilerRead ∧
                                      Cont normalizationRead substRead publicRead ∧
                                        hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchDescentRead branchAuditDescentRead descentBoundarySubstRead
    outputAuditReadiness readinessContinuationNormalization readinessProvenanceCompiler
    normalizationSubstPublic _substPkg publicPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, _transportUnary, continuationUnary, provenanceUnary, boundaryUnary,
      _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchDescentRead
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary auditUnary branchAuditDescentRead
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed descentReadUnary boundaryUnary descentBoundarySubstRead
  have readinessUnary : UnaryHistory readiness :=
    unary_cont_closed outputUnary auditUnary outputAuditReadiness
  have normalizationReadUnary : UnaryHistory normalizationRead :=
    unary_cont_closed readinessUnary continuationUnary readinessContinuationNormalization
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed readinessUnary provenanceUnary readinessProvenanceCompiler
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed normalizationReadUnary substReadUnary normalizationSubstPublic
  exact
    ⟨branchReadUnary, descentReadUnary, substReadUnary, readinessUnary,
      normalizationReadUnary, compilerReadUnary, publicReadUnary, branchDescentRead,
      branchAuditDescentRead, descentBoundarySubstRead, outputAuditReadiness,
      readinessContinuationNormalization, readinessProvenanceCompiler, normalizationSubstPublic,
      transportAuditContinuation, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
