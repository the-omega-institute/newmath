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

theorem AuthorizedGeneratorRecursorAuditProvenanceCover [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N provenanceRead consumerRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont A P provenanceRead ->
        Cont provenanceRead C consumerRead ->
          Cont consumerRead N terminalRead ->
            PkgSig bundle terminalRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    Cont A P provenanceRead ∧ Cont provenanceRead C consumerRead ∧
                      Cont consumerRead N terminalRead ∧ hsame row terminalRead)
                  (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
                  hsame ∧
                UnaryHistory A ∧ UnaryHistory P ∧ UnaryHistory provenanceRead ∧
                  UnaryHistory consumerRead ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier auditProvenanceRead provenanceConsumerRead consumerTerminalRead terminalPkg
  obtain ⟨_iUnary, _eUnary, _mUnary, _bUnary, _dUnary, _oUnary, auditUnary,
    _hUnary, continuationUnary, provenanceUnary, _gUnary, localNameUnary, _iEM,
    _mBD, _dOA, _hAC, _provenancePkg⟩ := carrier
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed auditUnary provenanceUnary auditProvenanceRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed provenanceReadUnary continuationUnary provenanceConsumerRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed consumerReadUnary localNameUnary consumerTerminalRead
  have sourceTerminal :
      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row) terminalRead := by
    exact ⟨hsame_refl terminalRead, terminalReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
        (fun row : BHist =>
          Cont A P provenanceRead ∧ Cont provenanceRead C consumerRead ∧
            Cont consumerRead N terminalRead ∧ hsame row terminalRead)
        (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead sourceTerminal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨auditProvenanceRead, provenanceConsumerRead, consumerTerminalRead, source.left⟩
    ledger_sound := by
      intro row source
      exact ⟨source.left, terminalPkg⟩
  }
  exact
    ⟨cert, auditUnary, provenanceUnary, provenanceReadUnary, consumerReadUnary,
      terminalReadUnary⟩

theorem AuthorizedGeneratorRecursorCarrier_audit_provenance_cover [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert auditRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont audit provenance auditRead ->
        Cont output auditRead publicRead ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row output ∨ hsame row audit ∨ hsame row provenance ∨
                    hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont audit provenance auditRead ∧
                    Cont output auditRead publicRead ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory auditRead ∧ UnaryHistory publicRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier auditProvenanceRead outputAuditRead publicPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
    outputUnary, auditUnary, _transportUnary, _continuationUnary, provenanceUnary,
    _boundaryUnary, _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportSame, provenancePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary provenanceUnary auditProvenanceRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary auditReadUnary outputAuditRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row output ∨ hsame row audit ∨ hsame row provenance ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont audit provenance auditRead ∧
              Cont output auditRead publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro row source
      exact ⟨source.right, auditProvenanceRead, outputAuditRead, publicPkg⟩
  }
  exact ⟨cert, auditReadUnary, publicReadUnary, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
