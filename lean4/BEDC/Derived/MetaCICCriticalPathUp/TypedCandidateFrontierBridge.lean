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

theorem MetaCICCriticalPathTypedCandidateFrontierBridge [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName typedFrontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont route localName typedFrontier →
        PkgSig bundle typedFrontier pkg →
          SemanticNameCert
              (fun row : BHist => hsame row typedFrontier ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row handoff ∨ hsame row obstruction ∨
                  hsame row dischargeSocket ∨ hsame row typedFrontier)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle typedFrontier pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory typedFrontier := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalName typedFrontierPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have typedFrontierUnary : UnaryHistory typedFrontier :=
    unary_cont_closed routeUnary localNameUnary routeLocalName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row typedFrontier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row handoff ∨ hsame row obstruction ∨
              hsame row dischargeSocket ∨ hsame row typedFrontier)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle typedFrontier pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro typedFrontier ⟨hsame_refl typedFrontier, typedFrontierUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, typedFrontierPkg, provenancePkg⟩
  }
  exact ⟨cert, typedFrontierUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
