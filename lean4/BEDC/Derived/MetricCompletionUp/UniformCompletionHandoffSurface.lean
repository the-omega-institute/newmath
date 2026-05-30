import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp.UniformCompletionHandoffSurface

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_uniform_completion_handoff_surface [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead uniformRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead readback uniformRead →
            Cont readback separated replay →
              Cont uniformRead replay scopeRead →
                PkgSig bundle scopeRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row selectedBranch ∨ hsame row readback ∨
                          hsame row separated ∨ hsame row replay ∨ hsame row uniformRead ∨
                            hsame row scopeRead)
                      (fun row : BHist =>
                        hsame row scopeRead ∧ PkgSig bundle scopeRead pkg)
                      hsame ∧
                    UnaryHistory selectedBranch ∧ UnaryHistory uniformRead ∧
                      UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro carrier selectedChoice sourceBranch branchReadback readbackSeparated uniformReplay
    scopePkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnaryCarrier, _provenanceUnary, _localCertUnary,
    _carrierReplayRoute, _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases selectedChoice with
    | inl sameFilter =>
        exact unary_transport_symm filterUnary sameFilter
    | inr sameNet =>
        exact unary_transport_symm netUnary sameNet
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary sourceBranch
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed branchReadUnary readbackUnary branchReadback
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed readbackUnary separatedUnary readbackSeparated
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed uniformUnary replayUnary uniformReplay
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row readback ∨
              hsame row separated ∨ hsame row replay ∨ hsame row uniformRead ∨
                hsame row scopeRead)
          (fun row : BHist => hsame row scopeRead ∧ PkgSig bundle scopeRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, scopePkg⟩
    }
  exact ⟨cert, selectedUnary, uniformUnary, scopeUnary⟩

end BEDC.Derived.MetricCompletionUp.UniformCompletionHandoffSurface
