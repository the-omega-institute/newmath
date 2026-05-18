import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOutputProvenanceCoverage [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      outputRead provenanceRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branches descent output audit
        transport routes provenance gap name bundle pkg ->
      Cont output audit outputRead ->
        Cont outputRead provenance provenanceRead ->
          Cont provenanceRead gap publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory outputRead ∧ UnaryHistory provenanceRead ∧
                UnaryHistory publicRead ∧ hsame transport (append audit routes) ∧
                  Cont output audit outputRead ∧ Cont outputRead provenance provenanceRead ∧
                    Cont provenanceRead gap publicRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier outputAuditRead outputReadProvenanceRead provenanceReadGapPublic publicPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchesUnary, _descentUnary,
      outputUnary, auditUnary, transportUnary, routesUnary, provenanceUnary, gapUnary,
      _nameUnary, _signatureEliminatorMotive, _motiveBranchesDescent, _descentOutputAudit,
      transportAuditRoutes, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed outputReadUnary provenanceUnary outputReadProvenanceRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed provenanceReadUnary gapUnary provenanceReadGapPublic
  exact
    ⟨outputReadUnary, provenanceReadUnary, publicReadUnary, transportAuditRoutes,
      outputAuditRead, outputReadProvenanceRead, provenanceReadGapPublic, provenancePkg,
      publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
