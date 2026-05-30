import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateNormalizationBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg ->
      Cont route handoff candidateBudget ->
        PkgSig bundle candidateBudget pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row candidateBudget ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row route ∨ hsame row handoff ∨ hsame row candidateBudget ∨
                  hsame row obstruction ∨ hsame row dischargeSocket)
              (fun row : BHist =>
                hsame row candidateBudget ∧ PkgSig bundle candidateBudget pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory candidateBudget ∧ UnaryHistory obstruction ∧
              UnaryHistory dischargeSocket ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeHandoffBudget candidateBudgetPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateBudgetUnary : UnaryHistory candidateBudget :=
    unary_cont_closed routeUnary handoffUnary routeHandoffBudget
  have sourceCandidateBudget :
      (fun row : BHist => hsame row candidateBudget ∧ UnaryHistory row)
        candidateBudget := by
    exact ⟨hsame_refl candidateBudget, candidateBudgetUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row candidateBudget ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row handoff ∨ hsame row candidateBudget ∨
              hsame row obstruction ∨ hsame row dischargeSocket)
          (fun row : BHist =>
            hsame row candidateBudget ∧ PkgSig bundle candidateBudget pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro candidateBudget sourceCandidateBudget
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, candidateBudgetPkg, provenancePkg⟩
  }
  exact ⟨cert, candidateBudgetUnary, obstructionUnary, dischargeSocketUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
