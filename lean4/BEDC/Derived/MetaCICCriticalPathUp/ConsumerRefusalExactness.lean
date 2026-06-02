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

theorem MetaCICCriticalPathConsumerRefusalExactness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont obstruction dischargeSocket refusalRead →
        PkgSig bundle refusalRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row refusalRead)
              (fun row : BHist =>
                hsame row refusalRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle refusalRead pkg)
              hsame ∧
            UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet obstructionSocketRefusal refusalPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed obstructionUnary dischargeSocketUnary obstructionSocketRefusal
  have sourceRefusal :
      (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row) refusalRead := by
    exact ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceRefusal
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
      exact ⟨source.left, provenancePkg, refusalPkg⟩
  }
  exact ⟨cert, refusalUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
