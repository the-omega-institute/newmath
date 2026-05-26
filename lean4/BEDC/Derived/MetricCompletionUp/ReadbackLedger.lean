import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.ReadbackLedger

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_finite_readback_ledger_nonescape [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance
      localCert exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      Cont readback separated replay →
        Cont replay localCert exportRead →
          PkgSig bundle exportRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row readback ∨ hsame row separated ∨ hsame row replay ∨
                    hsame row exportRead)
                (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                hsame ∧
              UnaryHistory readback ∧ UnaryHistory replay ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont UnaryHistory
  intro carrier replayRoute exportRoute exportPkg
  obtain ⟨_sourceUnary, _filterUnary, _netUnary, readbackUnary, separatedUnary,
    _transportUnary, replayUnaryCarrier, _provenanceUnary, localCertUnary,
    _carrierReplayRoute, _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed readbackUnary separatedUnary replayRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed replayUnary localCertUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∨ hsame row separated ∨ hsame row replay ∨
              hsame row exportRead)
          (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
        exact Or.inr (Or.inr (Or.inr sourceRow.left))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, exportPkg⟩
    }
  exact ⟨cert, readbackUnary, replayUnary, exportUnary⟩

end BEDC.Derived.MetricCompletionUp.ReadbackLedger
