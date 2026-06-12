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

theorem MetaCICCriticalPathSubjectReductionSocketCaseExhaustion
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead frontierRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName candidateRead →
        Cont candidateRead handoff frontierRead →
          Cont frontierRead obstruction socketRead →
            PkgSig bundle frontierRead pkg →
              PkgSig bundle socketRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row frontierRead ∨ hsame row socketRead ∨
                        hsame row dischargeSocket) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row frontierRead ∨
                        hsame row socketRead ∨ hsame row obstruction ∨
                          hsame row dischargeSocket)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                        PkgSig bundle socketRead pkg)
                    hsame ∧
                  UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet routeLocalNameCandidate candidateHandoffFrontier
    frontierObstructionSocket frontierPkg socketPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffFrontier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed frontierUnary obstructionUnary frontierObstructionSocket
  have sourceFrontier :
      (fun row : BHist =>
        (hsame row frontierRead ∨ hsame row socketRead ∨ hsame row dischargeSocket) ∧
          UnaryHistory row) frontierRead := by
    exact ⟨Or.inl (hsame_refl frontierRead), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row frontierRead ∨ hsame row socketRead ∨
              hsame row dischargeSocket) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨
              hsame row socketRead ∨ hsame row obstruction ∨
                hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle socketRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead sourceFrontier
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
        constructor
        · cases source.left with
          | inl frontierSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) frontierSame)
          | inr rest =>
              cases rest with
              | inl socketSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) socketSame))
              | inr dischargeSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) dischargeSame))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl frontierSame =>
          exact Or.inr (Or.inl frontierSame)
      | inr rest =>
          cases rest with
          | inl socketSame =>
              exact Or.inr (Or.inr (Or.inl socketSame))
          | inr dischargeSame =>
              exact Or.inr (Or.inr (Or.inr (Or.inr dischargeSame)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, socketPkg⟩
  }
  exact ⟨cert, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
