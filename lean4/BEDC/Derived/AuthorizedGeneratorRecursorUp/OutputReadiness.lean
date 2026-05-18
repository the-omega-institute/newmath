import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_output_readiness [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead descentRead outputRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont signature eliminator branchRead →
        Cont branchRead descent descentRead →
          Cont descentRead output outputRead →
            Cont outputRead continuation publicRead →
              PkgSig bundle publicRead pkg →
                UnaryHistory output ∧ UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                  UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                    Cont signature eliminator branchRead ∧
                      Cont branchRead descent descentRead ∧
                        Cont descentRead output outputRead ∧
                          Cont outputRead continuation publicRead ∧
                            hsame transport (append audit continuation) ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier signatureEliminatorRead branchReadDescentRead descentReadOutputRead
    outputReadContinuationPublic publicPkg
  rcases carrier with
    ⟨signatureUnary, eliminatorUnary, _motiveUnary, _branchUnary, descentUnary,
      outputUnary, _auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureEliminatorRead
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary descentUnary branchReadDescentRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary descentReadOutputRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary continuationUnary outputReadContinuationPublic
  exact
    ⟨outputUnary, branchReadUnary, descentReadUnary, outputReadUnary, publicReadUnary,
      signatureEliminatorRead, branchReadDescentRead, descentReadOutputRead,
      outputReadContinuationPublic, transportAuditContinuation, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
