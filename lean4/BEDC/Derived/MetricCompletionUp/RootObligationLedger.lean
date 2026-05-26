import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.RootObligationLedger

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_root_obligation_ledger [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead finiteReadback separatedRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead readback finiteReadback →
            Cont finiteReadback separated separatedRead →
              Cont separatedRead provenance ledgerRead →
                PkgSig bundle ledgerRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
                          hsame row finiteReadback ∨ hsame row separatedRead ∨
                            hsame row provenance ∨ hsame row ledgerRead)
                      (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
                      hsame ∧
                    UnaryHistory selectedBranch ∧ UnaryHistory branchRead ∧
                      UnaryHistory finiteReadback ∧ UnaryHistory separatedRead ∧
                        UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute readbackRoute separatedRoute ledgerRoute ledgerPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnary, provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have finiteReadbackUnary : UnaryHistory finiteReadback :=
    unary_cont_closed branchReadUnary readbackUnary readbackRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed finiteReadbackUnary separatedUnary separatedRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed separatedReadUnary provenanceUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row finiteReadback ∨ hsame row separatedRead ∨ hsame row provenance ∨
                hsame row ledgerRead)
          (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerReadUnary⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, ledgerPkg⟩
    }
  exact
    ⟨cert, selectedUnary, branchReadUnary, finiteReadbackUnary, separatedReadUnary,
      ledgerReadUnary⟩

end BEDC.Derived.MetricCompletionUp.RootObligationLedger
