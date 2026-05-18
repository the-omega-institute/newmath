import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootBranchRowExposure [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont B D branchRead →
        Cont D O outputRead →
          PkgSig bundle outputRead pkg →
            UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory branchRead ∧
              UnaryHistory outputRead ∧ Cont B D branchRead ∧ Cont D O outputRead ∧
                hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchDescentRead descentOutputRead outputPkg
  obtain ⟨_inputUnary, _elimUnary, _motiveUnary, branchUnary, descentUnary, outputUnary,
    _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary, _boundaryUnary,
    _localCertUnary, _inputElimMotive, _motiveBranchDescent, _descentOutputAudit,
    transportAuditContinuation, provenancePkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchDescentRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary descentOutputRead
  exact
    ⟨branchUnary, descentUnary, outputUnary, branchReadUnary, outputReadUnary,
      branchDescentRead, descentOutputRead, transportAuditContinuation, provenancePkg,
      outputPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
