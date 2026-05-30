import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp.BridgeSurfaceLock

open BEDC.Derived.MetricCompletionUp.NameCertObligations
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletion_bridge_surface_lock [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead readbackRead separatedRead uniformRead publicRead bridgeRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
      Cont source selectedBranch branchRead → Cont branchRead readback readbackRead →
      Cont readbackRead separated separatedRead → Cont separatedRead replay uniformRead →
      Cont uniformRead provenance publicRead → Cont publicRead localCert bridgeRead →
      PkgSig bundle bridgeRead pkg →
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row readbackRead ∨ hsame row separatedRead ∨ hsame row uniformRead ∨
                hsame row publicRead ∨ hsame row bridgeRead)
          (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame ∧
        UnaryHistory bridgeRead ∧ Cont publicRead localCert bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier selectedRoute sourceBranch branchReadRoute readbackSeparated separatedUniform
    uniformPublic publicLocal bridgePkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary, _transportUnary,
    replayUnary, provenanceUnary, localCertUnary, _carrierReplay, _transportSame,
    _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases selectedRoute with
    | inl selectedFilter =>
        exact unary_transport filterUnary (hsame_symm selectedFilter)
    | inr selectedNet =>
        exact unary_transport netUnary (hsame_symm selectedNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary sourceBranch
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed branchReadUnary readbackUnary branchReadRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed readbackReadUnary separatedUnary readbackSeparated
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed separatedReadUnary replayUnary separatedUniform
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed uniformReadUnary provenanceUnary uniformPublic
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicReadUnary localCertUnary publicLocal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row readbackRead ∨ hsame row separatedRead ∨ hsame row uniformRead ∨
                hsame row publicRead ∨ hsame row bridgeRead)
          (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeReadUnary⟩
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
      exact Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, bridgePkg⟩
  }
  exact ⟨cert, bridgeReadUnary, publicLocal⟩

end BEDC.Derived.MetricCompletionUp.BridgeSurfaceLock
