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

theorem MetaCICCriticalPathPacket_decidability_handoff_visibility [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff localName handoffRead →
        PkgSig bundle handoffRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row handoff ∨ hsame row localName ∨
                hsame row handoffRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle handoffRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory handoffRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet handoffLocalRead handoffReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalRead
  have sourceHandoffRead :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row handoff ∨ hsame row localName ∨
            hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle handoffRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoffRead
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, handoffReadPkg, provenancePkg⟩
  }
  exact ⟨cert, handoffReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
