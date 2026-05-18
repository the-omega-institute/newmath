import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAuditProvenanceFactorization [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont D O outputRead ->
        Cont outputRead A auditRead ->
          Cont auditRead C publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory outputRead ∧
                UnaryHistory auditRead ∧ UnaryHistory publicRead ∧ Cont D O outputRead ∧
                  Cont outputRead A auditRead ∧ Cont auditRead C publicRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier descentOutputRead outputReadAudit auditReadPublic publicPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, _transportAuditContinuation, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary descentOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary outputReadAudit
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed auditReadUnary continuationUnary auditReadPublic
  exact
    ⟨outputUnary, auditUnary, outputReadUnary, auditReadUnary, publicReadUnary,
      descentOutputRead, outputReadAudit, auditReadPublic, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
