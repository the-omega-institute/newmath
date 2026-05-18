import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_closed_substitution_consumer_lock
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead descentRead outputRead consumerRead lockedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont signature eliminator branchRead →
        Cont branchRead descent descentRead →
          Cont descentRead output outputRead →
            Cont outputRead continuation consumerRead →
              Cont consumerRead localCert lockedRead →
                PkgSig bundle lockedRead pkg →
                  UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                    UnaryHistory outputRead ∧ UnaryHistory consumerRead ∧
                      UnaryHistory lockedRead ∧ Cont signature eliminator branchRead ∧
                        Cont branchRead descent descentRead ∧
                          Cont descentRead output outputRead ∧
                            Cont outputRead continuation consumerRead ∧
                              Cont consumerRead localCert lockedRead ∧
                                hsame transport (append audit continuation) ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle lockedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier signatureEliminatorRead branchReadDescentRead descentReadOutputRead
    outputReadContinuationConsumer consumerLocalCertLocked lockedPkg
  rcases carrier with
    ⟨signatureUnary, eliminatorUnary, _motiveUnary, _branchUnary, descentUnary,
      outputUnary, _auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
      _descentOutputAudit, transportAuditContinuation, provenancePkg⟩
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureEliminatorRead
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary descentUnary branchReadDescentRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary descentReadOutputRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed outputReadUnary continuationUnary outputReadContinuationConsumer
  have lockedReadUnary : UnaryHistory lockedRead :=
    unary_cont_closed consumerReadUnary localCertUnary consumerLocalCertLocked
  exact
    ⟨branchReadUnary, descentReadUnary, outputReadUnary, consumerReadUnary, lockedReadUnary,
      signatureEliminatorRead, branchReadDescentRead, descentReadOutputRead,
      outputReadContinuationConsumer, consumerLocalCertLocked, transportAuditContinuation,
      provenancePkg, lockedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
