import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.SourceSeparatedScope

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_source_separated_scope [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead separatedRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead separated separatedRead →
            Cont separatedRead replay uniformRead →
              PkgSig bundle uniformRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row selectedBranch ∨ hsame row separated ∨
                        hsame row replay ∨ hsame row uniformRead)
                    (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                    hsame ∧
                  UnaryHistory source ∧ UnaryHistory selectedBranch ∧ UnaryHistory separated ∧
                    UnaryHistory replay ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute separatedRoute uniformRoute uniformPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, _readbackUnary, separatedUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed branchReadUnary separatedUnary separatedRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed separatedReadUnary replayUnary uniformRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row separated ∨
              hsame row replay ∨ hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, uniformPkg⟩
    }
  exact ⟨cert, sourceUnary, selectedUnary, separatedUnary, replayUnary, uniformUnary⟩

end BEDC.Derived.MetricCompletionUp.SourceSeparatedScope
