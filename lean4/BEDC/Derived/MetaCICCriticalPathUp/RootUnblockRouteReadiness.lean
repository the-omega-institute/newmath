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

theorem MetaCICCriticalPathRootUnblockRouteReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName routeRead →
        PkgSig bundle routeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                  hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                    hsame row routeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle routeRead pkg ∧
                  PkgSig bundle provenance pkg ∧ hsame transport localName)
              hsame ∧
            UnaryHistory routeRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalRead routeReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, transportLocalName,
    provenancePkg⟩ := packet
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row transport ∨
              hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle routeRead pkg ∧
              PkgSig bundle provenance pkg ∧ hsame transport localName)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro routeRead ⟨hsame_refl routeRead, routeReadUnary⟩
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
      exact ⟨source.right, routeReadPkg, provenancePkg, transportLocalName⟩
  }
  exact ⟨cert, routeReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
