import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAcceptedSignatureCover [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N signatureRead motiveRead branchRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont I E signatureRead →
        Cont signatureRead M motiveRead →
          Cont motiveRead B branchRead →
            Cont D O outputRead →
              PkgSig bundle outputRead pkg →
                UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
                  UnaryHistory signatureRead ∧ UnaryHistory motiveRead ∧
                    UnaryHistory branchRead ∧ UnaryHistory outputRead ∧
                      Cont I E signatureRead ∧ Cont signatureRead M motiveRead ∧
                        Cont motiveRead B branchRead ∧ Cont D O outputRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier signatureRoute motiveRoute branchRoute outputRoute outputPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportContinuation, provenancePkg⟩ := carrier
  have signatureReadUnary : UnaryHistory signatureRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureRoute
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed signatureReadUnary motiveUnary motiveRoute
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveReadUnary branchUnary branchRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary outputRoute
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, signatureReadUnary,
      motiveReadUnary, branchReadUnary, outputReadUnary, signatureRoute, motiveRoute,
      branchRoute, outputRoute, provenancePkg, outputPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
