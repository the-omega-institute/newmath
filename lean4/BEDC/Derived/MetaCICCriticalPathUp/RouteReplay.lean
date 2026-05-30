import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_route_replay [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route dischargeSocket replay →
        PkgSig bundle replay pkg →
          SemanticNameCert
              (fun row : BHist => hsame row replay ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont strongNorm normalForm route ∧
                  Cont handoff obstruction dischargeSocket ∧
                    (hsame row route ∨ hsame row dischargeSocket ∨ hsame row replay))
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle replay pkg ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeSocketReplay replayPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, _localNameUnary,
    strongNormNormalFormRoute, handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed routeUnary dischargeSocketUnary routeSocketReplay
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replay ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket ∧
              (hsame row route ∨ hsame row dischargeSocket ∨ hsame row replay))
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle replay pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨strongNormNormalFormRoute, handoffObstructionSocket,
          Or.inr (Or.inr source.left)⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayPkg, provenancePkg⟩
  }
  exact ⟨cert, replayUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
