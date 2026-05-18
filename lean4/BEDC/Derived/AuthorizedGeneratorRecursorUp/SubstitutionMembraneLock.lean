import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_substitution_membrane_lock [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert substitutionRead membraneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont output audit substitutionRead ->
        Cont substitutionRead continuation membraneRead ->
          PkgSig bundle membraneRead pkg ->
            UnaryHistory substitutionRead ∧ UnaryHistory membraneRead ∧
              Cont output audit substitutionRead ∧
                Cont substitutionRead continuation membraneRead ∧
                  hsame transport (append audit continuation) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle membraneRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAuditSubstitution substitutionContinuationMembrane membranePkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have substitutionUnary : UnaryHistory substitutionRead :=
    unary_cont_closed outputUnary auditUnary outputAuditSubstitution
  have membraneUnary : UnaryHistory membraneRead :=
    unary_cont_closed substitutionUnary continuationUnary substitutionContinuationMembrane
  exact
    ⟨substitutionUnary, membraneUnary, outputAuditSubstitution, substitutionContinuationMembrane,
      transportAuditContinuation, provenancePkg, membranePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
