import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.HandoffRoutes

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_filter_branch_handoff [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance
      localCert : BHist}
    {_exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      Cont source filterBranch readback →
        Cont readback separated replay →
          hsame replay provenance →
          PkgSig bundle provenance pkg →
            SemanticNameCert
                (fun row : BHist => hsame row replay ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row filterBranch ∨ hsame row readback ∨
                    hsame row separated ∨ hsame row replay)
                (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory source ∧ UnaryHistory filterBranch ∧ UnaryHistory readback ∧
                Cont source filterBranch readback ∧ Cont readback separated replay := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro carrier filterRoute separatedRoute replayToProvenance provenancePkg
  obtain ⟨sourceUnary, filterUnary, _netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnaryCarrier, _provenanceUnary, _localCertUnary,
    _carrierReplayRoute, _transportSame, _carrierProvenancePkg, _localCertPkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed readbackUnary separatedUnary separatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row filterBranch ∨ hsame row readback ∨
              hsame row separated ∨ hsame row replay)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro replay ⟨hsame_refl replay, replayUnary⟩
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
        exact ⟨hsame_trans sourceRow.left replayToProvenance, provenancePkg⟩
    }
  exact
    ⟨cert, sourceUnary, filterUnary, readbackUnary, filterRoute, separatedRoute⟩

end BEDC.Derived.MetricCompletionUp.HandoffRoutes
