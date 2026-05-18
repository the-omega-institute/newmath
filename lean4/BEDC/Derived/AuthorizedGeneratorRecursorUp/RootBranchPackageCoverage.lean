import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootBranchPackageCoverage [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead descentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont motive branch descentRead →
        Cont branch descent branchRead →
          PkgSig bundle provenance pkg →
            UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
              UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory branchRead ∧
                UnaryHistory descentRead ∧ Cont signature eliminator motive ∧
                  Cont motive branch descentRead ∧ Cont branch descent branchRead ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier motiveBranchDescentRead branchDescentBranchRead provenancePkg
  rcases carrier with
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
      _outputUnary, _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, _transportAuditContinuation, _carrierProvenancePkg⟩
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed motiveUnary branchUnary motiveBranchDescentRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchDescentBranchRead
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
      branchReadUnary, descentReadUnary, signatureEliminatorMotive, motiveBranchDescentRead,
      branchDescentBranchRead, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
