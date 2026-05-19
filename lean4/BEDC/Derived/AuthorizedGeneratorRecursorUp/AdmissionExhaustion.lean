import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAdmissionExhaustion [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert sigRead motiveRead branchRead descentRead outputRead auditRead handoff :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
      transport continuation provenance boundary localCert bundle pkg ->
      Cont signature eliminator sigRead ->
        Cont sigRead motive motiveRead ->
          Cont motiveRead branch branchRead ->
            Cont branchRead descent descentRead ->
              Cont descentRead output outputRead ->
                Cont outputRead audit auditRead ->
                  Cont audit continuation handoff ->
                    UnaryHistory handoff ∧ PkgSig bundle provenance pkg ∧
                      hsame transport (append audit continuation) ∧
                        SemanticNameCert
                          (fun h : BHist => hsame h localCert)
                          (fun h : BHist => hsame h localCert)
                          (fun h : BHist => hsame h localCert)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier signatureEliminatorSigRead sigReadMotiveMotiveRead
    motiveReadBranchBranchRead branchReadDescentDescentRead descentReadOutputOutputRead
    outputReadAuditAuditRead auditContinuationHandoff
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have sigReadUnary : UnaryHistory sigRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureEliminatorSigRead
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed sigReadUnary motiveUnary sigReadMotiveMotiveRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveReadUnary branchUnary motiveReadBranchBranchRead
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary descentUnary branchReadDescentDescentRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary descentReadOutputOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary outputReadAuditAuditRead
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed auditUnary continuationUnary auditContinuationHandoff
  have localSource : (fun h : BHist => hsame h localCert) localCert :=
    hsame_refl localCert
  have localCertSemantic :
      SemanticNameCert
        (fun h : BHist => hsame h localCert)
        (fun h : BHist => hsame h localCert)
        (fun h : BHist => hsame h localCert)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro localCert localSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨handoffUnary, provenancePkg, transportAuditContinuation, localCertSemantic⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
