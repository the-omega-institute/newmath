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

theorem AuthorizedGeneratorRecursorOutputReadinessBridgeDeterminacy [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N routeRead transportRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O A routeRead →
        Cont routeRead H transportRead →
          Cont transportRead N boundaryRead →
            PkgSig bundle boundaryRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row B ∨ hsame row O ∨ hsame row A ∨
                      hsame row boundaryRead)
                  (fun row : BHist =>
                    hsame row boundaryRead ∧ PkgSig bundle boundaryRead pkg)
                  hsame ∧
                UnaryHistory routeRead ∧ UnaryHistory transportRead ∧
                  UnaryHistory boundaryRead ∧ Cont O A routeRead ∧
                    Cont routeRead H transportRead ∧ Cont transportRead N boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier outputAuditRoute routeTransport transportBoundary boundaryPkg
  obtain ⟨_IUnary, _EUnary, _MUnary, _BUnary, _DUnary, outputUnary, auditUnary,
    transportUnary, _continuationUnary, _provenanceUnary, _boundaryUnary, nameUnary,
    _signatureEliminatorMotive, _motiveBranchDescent, _descentOutputAudit,
    _transportAuditContinuation, _provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRoute
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed routeUnary transportUnary routeTransport
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed transportReadUnary nameUnary transportBoundary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row I ∨ hsame row B ∨ hsame row O ∨ hsame row A ∨
            hsame row boundaryRead)
        (fun row : BHist => hsame row boundaryRead ∧ PkgSig bundle boundaryRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundaryPkg⟩
  }
  exact
    ⟨cert, routeUnary, transportReadUnary, boundaryReadUnary, outputAuditRoute,
      routeTransport, transportBoundary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
