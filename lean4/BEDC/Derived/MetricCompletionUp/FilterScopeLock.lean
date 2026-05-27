import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp.FilterScopeLock

open BEDC.Derived.MetricCompletionUp.NameCertObligations
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletion_filter_scope_lock [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      branchRead readbackRead separatedRead replayRead provenanceRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      Cont source filterBranch branchRead → Cont branchRead readback readbackRead →
      Cont readbackRead separated separatedRead → Cont separatedRead replay replayRead →
      Cont replayRead provenance provenanceRead → Cont provenanceRead localCert scopeRead →
      PkgSig bundle scopeRead pkg →
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filterBranch ∨ hsame row branchRead ∨ hsame row readbackRead ∨
              hsame row separatedRead ∨ hsame row replayRead ∨ hsame row provenanceRead ∨
                hsame row scopeRead)
          (fun row : BHist => hsame row scopeRead ∧ PkgSig bundle scopeRead pkg)
          hsame ∧
        UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier sourceFilter filterReadback readbackSeparated separatedReplay replayProvenance
    provenanceLocal scopePkg
  obtain ⟨sourceUnary, filterUnary, _netUnary, readbackUnary, separatedUnary,
    _transportUnary, replayUnary, provenanceUnary, localCertUnary, _carrierReplay,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary filterUnary sourceFilter
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed branchReadUnary readbackUnary filterReadback
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed readbackReadUnary separatedUnary readbackSeparated
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed separatedReadUnary replayUnary separatedReplay
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed replayReadUnary provenanceUnary replayProvenance
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed provenanceReadUnary localCertUnary provenanceLocal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filterBranch ∨ hsame row branchRead ∨ hsame row readbackRead ∨
              hsame row separatedRead ∨ hsame row replayRead ∨ hsame row provenanceRead ∨
                hsame row scopeRead)
          (fun row : BHist => hsame row scopeRead ∧ PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeReadUnary⟩
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
      exact ⟨sourceRow.left, scopePkg⟩
  }
  exact ⟨cert, scopeReadUnary⟩

end BEDC.Derived.MetricCompletionUp.FilterScopeLock
