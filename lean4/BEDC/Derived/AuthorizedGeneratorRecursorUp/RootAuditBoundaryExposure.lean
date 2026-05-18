import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootAuditBoundaryExposure [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap
      localName outputRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branches descent output audit
        transport routes provenance gap localName bundle pkg →
      Cont output audit outputRead →
        Cont audit gap auditRead →
          PkgSig bundle auditRead pkg →
            UnaryHistory audit ∧ UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
              Cont output audit outputRead ∧ Cont audit gap auditRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                  hsame localName localName := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier outputAuditRead auditGapRead auditReadPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchesUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, _routesUnary, _provenanceUnary, gapUnary,
      _localNameUnary, _signatureEliminatorMotive, _motiveBranchesDescent,
      _descentOutputAudit, _transportAuditRoutes, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary gapUnary auditGapRead
  exact
    ⟨auditUnary, outputReadUnary, auditReadUnary, outputAuditRead, auditGapRead,
      provenancePkg, auditReadPkg, hsame_refl localName⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
