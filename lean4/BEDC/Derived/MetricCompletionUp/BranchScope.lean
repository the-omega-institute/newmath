import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.BranchScope

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_filter_branch_scope [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      filterRead readbackRead separatedRead comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      Cont source filterBranch filterRead →
        Cont filterRead readback readbackRead →
          Cont readback separated separatedRead →
            Cont separatedRead transport comparisonRead →
              PkgSig bundle comparisonRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row filterBranch ∨ hsame row filterRead ∨
                        hsame row readbackRead ∨ hsame row separatedRead ∨
                          hsame row comparisonRead)
                    (fun row : BHist =>
                      hsame row comparisonRead ∧ PkgSig bundle comparisonRead pkg)
                    hsame ∧
                  UnaryHistory source ∧ UnaryHistory filterBranch ∧
                    UnaryHistory filterRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory separatedRead ∧ UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier sourceToFilter filterToReadback readbackToSeparated separatedToTransport
    comparisonPkg
  obtain ⟨sourceUnary, filterUnary, _netUnary, readbackUnary, separatedUnary,
    transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed sourceUnary filterUnary sourceToFilter
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed filterReadUnary readbackUnary filterToReadback
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed readbackUnary separatedUnary readbackToSeparated
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed separatedReadUnary transportUnary separatedToTransport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row filterBranch ∨ hsame row filterRead ∨
              hsame row readbackRead ∨ hsame row separatedRead ∨
                hsame row comparisonRead)
          (fun row : BHist => hsame row comparisonRead ∧ PkgSig bundle comparisonRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro comparisonRead ⟨hsame_refl comparisonRead, comparisonReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, comparisonPkg⟩
    }
  exact
    ⟨cert, sourceUnary, filterUnary, filterReadUnary, readbackReadUnary, separatedReadUnary,
      comparisonReadUnary⟩

theorem MetricCompletion_net_branch_scope [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      netRead readbackRead separatedRead comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      Cont source netBranch netRead →
        Cont netRead readback readbackRead →
          Cont readback separated separatedRead →
            Cont separatedRead transport comparisonRead →
              PkgSig bundle comparisonRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row netBranch ∨ hsame row netRead ∨
                        hsame row readbackRead ∨ hsame row separatedRead ∨
                          hsame row comparisonRead)
                    (fun row : BHist =>
                      hsame row comparisonRead ∧ PkgSig bundle comparisonRead pkg)
                    hsame ∧
                  UnaryHistory source ∧ UnaryHistory netBranch ∧ UnaryHistory netRead ∧
                    UnaryHistory readbackRead ∧ UnaryHistory separatedRead ∧
                      UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier sourceToNet netToReadback readbackToSeparated separatedToTransport
    comparisonPkg
  obtain ⟨sourceUnary, _filterUnary, netUnary, readbackUnary, separatedUnary,
    transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed sourceUnary netUnary sourceToNet
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed netReadUnary readbackUnary netToReadback
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed readbackUnary separatedUnary readbackToSeparated
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed separatedReadUnary transportUnary separatedToTransport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row netBranch ∨ hsame row netRead ∨
              hsame row readbackRead ∨ hsame row separatedRead ∨
                hsame row comparisonRead)
          (fun row : BHist => hsame row comparisonRead ∧ PkgSig bundle comparisonRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro comparisonRead ⟨hsame_refl comparisonRead, comparisonReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, comparisonPkg⟩
    }
  exact
    ⟨cert, sourceUnary, netUnary, netReadUnary, readbackReadUnary, separatedReadUnary,
      comparisonReadUnary⟩

end BEDC.Derived.MetricCompletionUp.BranchScope
