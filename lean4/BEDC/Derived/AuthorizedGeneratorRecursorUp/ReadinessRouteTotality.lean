import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorReadinessRouteTotality [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert sigRead motiveRead branchRead outputRead auditRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont signature eliminator sigRead →
        Cont sigRead motive motiveRead →
          Cont motiveRead branch branchRead →
            Cont descent output outputRead →
              Cont outputRead audit auditRead →
                Cont audit continuation handoff →
                  PkgSig bundle provenance pkg →
                    UnaryHistory sigRead ∧ UnaryHistory motiveRead ∧
                      UnaryHistory branchRead ∧ UnaryHistory outputRead ∧
                        UnaryHistory auditRead ∧ UnaryHistory handoff ∧
                          hsame transport (append audit continuation) ∧
                            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier signatureEliminatorSigRead sigReadMotiveMotiveRead
    motiveReadBranchBranchRead descentOutputOutputRead outputReadAuditAuditRead
    auditContinuationHandoff provenancePkg
  rcases carrier with
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, _transportUnary, continuationUnary, _provenanceUnary, _boundaryUnary,
      _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, _carrierProvenancePkg⟩
  have sigReadUnary : UnaryHistory sigRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureEliminatorSigRead
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed sigReadUnary motiveUnary sigReadMotiveMotiveRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveReadUnary branchUnary motiveReadBranchBranchRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary descentOutputOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary outputReadAuditAuditRead
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed auditUnary continuationUnary auditContinuationHandoff
  exact
    ⟨sigReadUnary, motiveReadUnary, branchReadUnary, outputReadUnary, auditReadUnary,
      handoffUnary, transportAuditContinuation, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
