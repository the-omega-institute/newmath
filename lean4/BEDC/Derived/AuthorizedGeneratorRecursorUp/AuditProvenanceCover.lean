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

end BEDC.Derived.AuthorizedGeneratorRecursorUp
