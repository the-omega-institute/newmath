import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorScopePackage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N signatureRead branchRead outputRead auditRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E signatureRead ->
        Cont M B branchRead ->
          Cont D O outputRead ->
            Cont outputRead A auditRead ->
              Cont auditRead C publicRead ->
                PkgSig bundle publicRead pkg ->
                  UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
                    UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧
                      UnaryHistory signatureRead ∧ UnaryHistory branchRead ∧
                        UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                          UnaryHistory publicRead ∧ Cont I E signatureRead ∧
                            Cont M B branchRead ∧ Cont D O outputRead ∧
                              Cont outputRead A auditRead ∧ Cont auditRead C publicRead ∧
                                hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier signatureRoute branchRoute outputRoute auditRoute publicRoute publicPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, transportUnary, continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have signatureReadUnary : UnaryHistory signatureRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveUnary branchUnary branchRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary outputRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary auditRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed auditReadUnary continuationUnary publicRoute
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, signatureReadUnary, branchReadUnary, outputReadUnary, auditReadUnary,
      publicReadUnary, signatureRoute, branchRoute, outputRoute, auditRoute, publicRoute,
      transportAuditContinuation, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
