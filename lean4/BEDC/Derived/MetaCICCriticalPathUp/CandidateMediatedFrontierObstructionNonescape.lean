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

theorem MetaCICCriticalPathCandidateMediatedFrontierObstructionNonescape
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName frontierRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont strongNorm normalForm frontierRead ->
        Cont handoff obstruction socketRead ->
          PkgSig bundle socketRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row frontierRead ∨ hsame row socketRead ∨ hsame row obstruction ∨
                    hsame row dischargeSocket) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row frontierRead ∨ hsame row socketRead ∨ hsame row obstruction ∨
                    hsame row dischargeSocket)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory frontierRead ∧ UnaryHistory socketRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalFormFrontier handoffObstructionSocket socketPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormFrontier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionSocket
  have sourceFrontier :
      (fun row : BHist =>
        (hsame row frontierRead ∨ hsame row socketRead ∨ hsame row obstruction ∨
          hsame row dischargeSocket) ∧ UnaryHistory row) frontierRead := by
    exact ⟨Or.inl (hsame_refl frontierRead), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row frontierRead ∨ hsame row socketRead ∨ hsame row obstruction ∨
              hsame row dischargeSocket) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontierRead ∨ hsame row socketRead ∨ hsame row obstruction ∨
              hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              PkgSig bundle provenance pkg)
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
          | inl sameFrontier =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier)
          | inr rest =>
              cases rest with
              | inl sameSocket =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSocket))
              | inr rest =>
                  cases rest with
                  | inl sameObstruction =>
                      exact
                        Or.inr (Or.inr (Or.inl
                          (hsame_trans (hsame_symm sameRows) sameObstruction)))
                  | inr sameDischargeSocket =>
                      exact
                        Or.inr (Or.inr (Or.inr
                          (hsame_trans (hsame_symm sameRows) sameDischargeSocket)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketPkg, provenancePkg⟩
  }
  exact ⟨cert, frontierUnary, socketUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
