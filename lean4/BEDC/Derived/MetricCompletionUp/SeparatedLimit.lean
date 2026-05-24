import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.SeparatedLimit

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_separated_limit_uniqueness [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance
      localCert leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      Cont readback separated replay →
        hsame leftRead separated →
          hsame rightRead separated →
            hsame separated provenance →
            hsame leftRead rightRead ∧
              SemanticNameCert
                  (fun row : BHist => hsame row separated ∧ UnaryHistory separated)
                  (fun row : BHist =>
                    hsame row readback ∨ hsame row separated ∨ hsame row replay)
                  (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro carrier separatedRoute leftSame rightSame separatedToProvenance
  obtain ⟨_sourceUnary, _filterUnary, _netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnaryCarrier, _provenanceUnary, _localCertUnary,
    _carrierReplayRoute, _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed readbackUnary separatedUnary separatedRoute
  have leftRight : hsame leftRead rightRead :=
    hsame_trans leftSame (hsame_symm rightSame)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separated ∧ UnaryHistory separated)
          (fun row : BHist => hsame row readback ∨ hsame row separated ∨ hsame row replay)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro separated ⟨hsame_refl separated, separatedUnary⟩
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
          exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inl sourceRow.left)
      ledger_sound := by
        intro _row sourceRow
        exact ⟨hsame_trans sourceRow.left separatedToProvenance, provenancePkg⟩
    }
  exact ⟨leftRight, cert⟩

end BEDC.Derived.MetricCompletionUp.SeparatedLimit
