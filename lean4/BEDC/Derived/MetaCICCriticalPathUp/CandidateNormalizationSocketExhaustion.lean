import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateNormalizationSocketExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport route
        provenance localName bundle pkg →
      Cont handoff obstruction candidateRead →
        PkgSig bundle candidateRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row candidateRead ∧ UnaryHistory row)
              (fun row : BHist =>
                UnaryHistory row ∧ (hsame row candidateRead ∨ hsame row dischargeSocket))
              (fun _row : BHist => PkgSig bundle candidateRead pkg ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory candidateRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet handoffObstructionCandidate candidatePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionCandidate
  have sourceCandidate :
      (fun row : BHist => hsame row candidateRead ∧ UnaryHistory row) candidateRead := by
    exact ⟨hsame_refl candidateRead, candidateUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row candidateRead ∧ UnaryHistory row)
          (fun row : BHist =>
            UnaryHistory row ∧ (hsame row candidateRead ∨ hsame row dischargeSocket))
          (fun _row : BHist => PkgSig bundle candidateRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro candidateRead sourceCandidate
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
      exact ⟨source.right, Or.inl source.left⟩
    ledger_sound := by
      intro _row _source
      exact ⟨candidatePkg, provenancePkg⟩
  }
  exact ⟨cert, candidateUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
