import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootBranchRowTotality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead outputRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont D O outputRead ->
          Cont branchRead outputRead publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory branchRead ∧
                UnaryHistory outputRead ∧ UnaryHistory publicRead ∧ hsame H (append A C) ∧
                  Cont B D branchRead ∧ Cont D O outputRead ∧
                    Cont branchRead outputRead publicRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchRoute outputRoute publicRoute publicPkg
  obtain ⟨_inputUnary, _eliminatorUnary, _motiveUnary, branchUnary, descentUnary,
    outputUnary, _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _inputEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary outputRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchReadUnary outputReadUnary publicRoute
  exact
    ⟨branchUnary, descentUnary, outputUnary, branchReadUnary, outputReadUnary,
      publicReadUnary, transportAuditContinuation, branchRoute, outputRoute, publicRoute,
      provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
